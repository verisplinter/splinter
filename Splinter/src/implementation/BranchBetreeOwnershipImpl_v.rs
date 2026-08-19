// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_multisets_equal;
use vstd::assert_sets_equal;
use vstd::set_lib::{
    lemma_int_range, lemma_set_subset_finite, set_int_range,
};
use vstd::map_lib::lemma_values_finite;

use crate::allocation_layer::BranchTypes_v::Summary;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::Likes_v::AULikes;
use crate::disk::GenericDisk_v::{AU, IAU};
use crate::implementation::AuLikesImpl_v::{
    iau_seq_set, seq_to_au_likes, unique_iau_seq,
};

verus! {

proof fn iau_seq_set_push(aus: Seq<IAU>, au: IAU)
    ensures
        iau_seq_set(aus.push(au)) =~= iau_seq_set(aus).insert(au as nat),
{
    assert forall |candidate: AU|
        #![trigger iau_seq_set(aus.push(au)).contains(candidate)]
        iau_seq_set(aus.push(au)).contains(candidate)
        == iau_seq_set(aus).insert(au as nat).contains(candidate) by {
        if iau_seq_set(aus.push(au)).contains(candidate) {
            let i = choose |i: int| #![auto]
                0 <= i < aus.push(au).len()
                && aus.push(au)[i] as nat == candidate;
            if i < aus.len() {
                assert(aus.push(au)[i] == aus[i]);
                assert(iau_seq_set(aus).contains(candidate));
            } else {
                assert(i == aus.len());
                assert(aus.push(au)[i] == au);
            }
        } else if iau_seq_set(aus).insert(au as nat).contains(candidate) {
            if candidate == au as nat {
                assert(aus.push(au)[aus.len() as int] == au);
                assert(iau_seq_set(aus.push(au)).contains(candidate));
            } else {
                let i = choose |i: int| #![auto]
                    0 <= i < aus.len() && aus[i] as nat == candidate;
                assert(aus.push(au)[i] == aus[i]);
                assert(iau_seq_set(aus.push(au)).contains(candidate));
            }
        }
    }
}

proof fn iau_seq_set_singleton(au: IAU)
    ensures iau_seq_set(seq![au]) =~= set![au as nat],
{
    iau_seq_set_push(Seq::<IAU>::empty(), au);
    assert(iau_seq_set(Seq::<IAU>::empty()) =~= Set::<AU>::empty()) by {
        assert forall |candidate: AU|
            #![trigger iau_seq_set(Seq::<IAU>::empty()).contains(candidate)]
            !iau_seq_set(Seq::<IAU>::empty()).contains(candidate) by {
        }
    }
}

proof fn iau_seq_set_pair(left: IAU, right: IAU)
    requires left != right,
    ensures
        unique_iau_seq(seq![left, right]),
        iau_seq_set(seq![left, right]) =~= set![left as nat, right as nat],
{
    iau_seq_set_singleton(left);
    iau_seq_set_push(seq![left], right);
}

pub fn iau_vec_unique(aus: &Vec<IAU>) -> (out: bool)
    ensures out == unique_iau_seq(aus@),
{
    let mut i = 0usize;
    while i < aus.len()
        invariant
            i <= aus.len(),
            forall |left: int, right: int|
                #![trigger aus@[left], aus@[right]]
                0 <= left < i
                && 0 <= right < aus@.len()
                && aus@[left] == aus@[right]
                ==> left == right,
        decreases aus.len() - i,
    {
        let mut j = 0usize;
        while j < aus.len()
            invariant
                i < aus.len(),
                j <= aus.len(),
                forall |right: int| #![trigger aus@[right]]
                    0 <= right < j
                    && aus@[i as int] == aus@[right]
                    ==> i as int == right,
            decreases aus.len() - j,
        {
            if i != j && aus[i] == aus[j] {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

proof fn unique_iau_seq_likes_count(aus: Seq<IAU>, query: AU)
    requires unique_iau_seq(aus),
    ensures
        seq_to_au_likes(aus).count(query)
            == if iau_seq_set(aus).contains(query) { 1nat } else { 0nat },
    decreases aus.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    if aus.len() > 0 {
        let prefix = aus.drop_last();
        let last = aus.last();
        assert(unique_iau_seq(prefix)) by {
            assert forall |i: int, j: int| #![trigger prefix[i], prefix[j]]
                0 <= i < prefix.len()
                && 0 <= j < prefix.len()
                && prefix[i] == prefix[j]
                implies i == j by {
                assert(prefix[i] == aus[i]);
                assert(prefix[j] == aus[j]);
            }
        }
        assert(!iau_seq_set(prefix).contains(last as nat)) by {
            if iau_seq_set(prefix).contains(last as nat) {
                let i = choose |i: int| #![auto]
                    0 <= i < prefix.len() && prefix[i] == last;
                assert(prefix[i] == aus[i]);
                assert(aus.last() == aus[aus.len() - 1]);
                assert(i != aus.len() - 1);
            }
        }
        unique_iau_seq_likes_count(prefix, query);
        assert(aus == prefix.push(last));
        iau_seq_set_push(prefix, last);
    }
}

pub open spec fn betree_batch_replace_applicable(
    ownership: BranchBetreeOwnershipImpl,
    old_aus: Seq<IAU>,
    new_aus: Seq<IAU>,
) -> bool {
    &&& unique_iau_seq(old_aus)
    &&& unique_iau_seq(new_aus)
    &&& iau_seq_set(old_aus) <= ownership.betree.active_aus()
    &&& ownership.betree.all_aus().disjoint(iau_seq_set(new_aus))
    &&& ownership.branches.all_summary_aus().disjoint(iau_seq_set(new_aus))
}

pub open spec fn branch_batch_retire_applicable(
    ownership: BranchSummaryOwnershipImpl,
    roots: Seq<IAU>,
) -> bool {
    &&& unique_iau_seq(roots)
    &&& iau_seq_set(roots) <= ownership.active_summary_map().dom()
}

pub fn append_unique_aus(out: &mut Vec<IAU>, input: Vec<IAU>)
    requires
        unique_iau_seq(old(out)@),
        unique_iau_seq(input@),
        iau_seq_set(old(out)@).disjoint(iau_seq_set(input@)),
    ensures
        out@ == old(out)@ + input@,
        unique_iau_seq(out@),
        iau_seq_set(out@)
            =~= iau_seq_set(old(out)@) + iau_seq_set(input@),
{
    let ghost initial = out@;
    let mut index = 0usize;
    while index < input.len()
        invariant
            index <= input.len(),
            out@ == initial + input@.take(index as int),
            unique_iau_seq(out@),
            iau_seq_set(out@)
                =~= iau_seq_set(initial)
                    + iau_seq_set(input@.take(index as int)),
        decreases input.len() - index,
    {
        let au = input[index];
        let ghost before = out@;
        proof {
            assert(!iau_seq_set(out@).contains(au as nat)) by {
                if iau_seq_set(initial).contains(au as nat) {
                    assert(iau_seq_set(initial).disjoint(iau_seq_set(input@)));
                    assert(iau_seq_set(input@).contains(au as nat));
                } else if iau_seq_set(input@.take(index as int)).contains(au as nat) {
                    let earlier = choose |i: int| #![auto]
                        0 <= i < input@.take(index as int).len()
                        && input@.take(index as int)[i] == au;
                    assert(input@[earlier] == input@[index as int]);
                    assert(earlier != index);
                }
            }
        }
        out.push(au);
        proof {
            assert(out@ == before.push(au));
            iau_seq_set_push(before, au);
            assert(unique_iau_seq(out@));
            assert(input@.take(index as int + 1)
                == input@.take(index as int).push(au));
            iau_seq_set_push(input@.take(index as int), au);
            assert(iau_seq_set(out@)
                =~= iau_seq_set(initial)
                    + iau_seq_set(input@.take(index as int + 1)));
        }
        index += 1;
    }
    proof { assert(input@.take(index as int) == input@); }
}

fn copy_iau_vec(input: &Vec<IAU>) -> (out: Vec<IAU>)
    ensures out@ == input@,
{
    let mut out = Vec::<IAU>::new();
    let mut index = 0usize;
    while index < input.len()
        invariant
            index <= input.len(),
            out@ == input@.take(index as int),
        decreases input.len() - index,
    {
        out.push(input[index]);
        index += 1;
    }
    proof { assert(input@.take(index as int) == input@); }
    out
}

proof fn disjoint_component_reclaims(
    left_universe: Set<AU>,
    left_persistent: Set<AU>,
    left_frozen: Set<AU>,
    left_current: Set<AU>,
    right_universe: Set<AU>,
    right_persistent: Set<AU>,
    right_frozen: Set<AU>,
    right_current: Set<AU>,
)
    requires
        left_universe.disjoint(right_universe),
        left_persistent <= left_universe,
        left_frozen <= left_universe,
        left_current <= left_universe,
        right_persistent <= right_universe,
        right_frozen <= right_universe,
        right_current <= right_universe,
    ensures
        (left_persistent - left_frozen - left_current)
            + (right_persistent - right_frozen - right_current)
        =~= (left_persistent + right_persistent)
            - (left_frozen + right_frozen)
            - (left_current + right_current),
{
    assert forall |au: AU|
        #![trigger ((left_persistent - left_frozen - left_current)
            + (right_persistent - right_frozen - right_current)).contains(au)]
        ((left_persistent - left_frozen - left_current)
            + (right_persistent - right_frozen - right_current)).contains(au)
        == ((left_persistent + right_persistent)
            - (left_frozen + right_frozen)
            - (left_current + right_current)).contains(au) by {
        if left_universe.contains(au) {
            assert(!right_universe.contains(au));
        } else if right_universe.contains(au) {
            assert(!left_universe.contains(au));
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SnapshotMembership {
    pub persistent: bool,
    pub frozen: bool,
}

impl SnapshotMembership {
    pub open spec fn unprotected(self) -> bool {
        !self.persistent && !self.frozen
    }

    pub open spec fn protected(self) -> bool {
        self.persistent || self.frozen
    }

    pub open spec fn freeze(self) -> Self {
        Self { persistent: self.persistent, frozen: true }
    }

    pub open spec fn commit_complete(self) -> Self {
        Self { persistent: self.frozen, frozen: false }
    }

    pub fn ephemeral() -> (out: Self)
        ensures out == (Self { persistent: false, frozen: false }),
    {
        Self { persistent: false, frozen: false }
    }

    pub fn recovered() -> (out: Self)
        ensures out == (Self { persistent: true, frozen: false }),
    {
        Self { persistent: true, frozen: false }
    }

    fn mark_frozen(&mut self)
        ensures
            self.persistent == old(self).persistent,
            self.frozen,
    {
        self.frozen = true;
    }

    fn finish_commit(&mut self)
        ensures
            self.persistent == old(self).frozen,
            !self.frozen,
    {
        self.persistent = self.frozen;
        self.frozen = false;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BetreeAuRecord {
    pub au: IAU,
    pub snapshots: SnapshotMembership,
}

pub struct BranchSummaryRecord {
    pub root_au: IAU,
    pub summary: Vec<IAU>,
    pub snapshots: SnapshotMembership,
}

pub struct BetreeAuBucket {
    pub entries: Vec<BetreeAuRecord>,
}

pub struct BetreeAuTable {
    pub buckets: Vec<BetreeAuBucket>,
    pub bucket_count: u32,
}

pub struct BetreeAuOwnershipImpl {
    pub active: BetreeAuTable,
    pub retired: BetreeAuTable,
}

pub struct BranchBetreeOwnershipImpl {
    pub betree: BetreeAuOwnershipImpl,
    pub branches: BranchSummaryOwnershipImpl,
}

#[derive(Debug)]
pub enum BetreeOwnershipUpdateResult {
    Applied { reclaimed: Vec<IAU> },
    Noop,
}

pub open spec fn freeze_betree_selected(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
) -> Map<AU, SnapshotMembership> {
    Map::new(
        |au: AU| initial.contains_key(au),
        |au: AU| if selected.contains(au) {
            initial[au].freeze()
        } else {
            initial[au]
        },
    )
}

pub open spec fn commit_active_betree_selected(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
) -> Map<AU, SnapshotMembership> {
    Map::new(
        |au: AU| initial.contains_key(au),
        |au: AU| if selected.contains(au) {
            initial[au].commit_complete()
        } else {
            initial[au]
        },
    )
}

pub open spec fn commit_retired_betree_selected(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
) -> Map<AU, SnapshotMembership> {
    Map::new(
        |au: AU| initial.contains_key(au)
            && (!selected.contains(au) || initial[au].frozen),
        |au: AU| if selected.contains(au) {
            initial[au].commit_complete()
        } else {
            initial[au]
        },
    )
}

pub open spec fn retired_betree_reclaimed_set(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
) -> Set<AU> {
    Set::new(|au: AU| initial.contains_key(au)
        && selected.contains(au)
        && !initial[au].frozen)
}

proof fn freeze_selected_insert(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
    au: AU,
)
    requires
        initial.contains_key(au),
        !selected.contains(au),
    ensures
        freeze_betree_selected(initial, selected).insert(
            au,
            initial[au].freeze(),
        ) == freeze_betree_selected(initial, selected.insert(au)),
{
    assert_maps_equal!(
        freeze_betree_selected(initial, selected).insert(
            au,
            initial[au].freeze(),
        ),
        freeze_betree_selected(initial, selected.insert(au)),
        candidate => { }
    );
}

proof fn commit_active_selected_insert(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
    au: AU,
)
    requires
        initial.contains_key(au),
        !selected.contains(au),
    ensures
        commit_active_betree_selected(initial, selected).insert(
            au,
            initial[au].commit_complete(),
        ) == commit_active_betree_selected(initial, selected.insert(au)),
{
    assert_maps_equal!(
        commit_active_betree_selected(initial, selected).insert(
            au,
            initial[au].commit_complete(),
        ),
        commit_active_betree_selected(initial, selected.insert(au)),
        candidate => { }
    );
}

proof fn commit_retired_selected_insert(
    initial: Map<AU, SnapshotMembership>,
    selected: Set<AU>,
    au: AU,
)
    requires
        initial.contains_key(au),
        !selected.contains(au),
    ensures
        (if initial[au].frozen {
            commit_retired_betree_selected(initial, selected).insert(
                au,
                initial[au].commit_complete(),
            )
        } else {
            commit_retired_betree_selected(initial, selected).remove(au)
        }) == commit_retired_betree_selected(initial, selected.insert(au)),
        retired_betree_reclaimed_set(initial, selected.insert(au))
            =~= if initial[au].frozen {
                retired_betree_reclaimed_set(initial, selected)
            } else {
                retired_betree_reclaimed_set(initial, selected).insert(au)
            },
{
    assert_maps_equal!(
        if initial[au].frozen {
            commit_retired_betree_selected(initial, selected).insert(
                au,
                initial[au].commit_complete(),
            )
        } else {
            commit_retired_betree_selected(initial, selected).remove(au)
        },
        commit_retired_betree_selected(initial, selected.insert(au)),
        candidate => { }
    );
    assert forall |candidate: AU|
        #![trigger retired_betree_reclaimed_set(
            initial,
            selected.insert(au),
        ).contains(candidate)]
        retired_betree_reclaimed_set(initial, selected.insert(au))
            .contains(candidate)
        == (if initial[au].frozen {
            retired_betree_reclaimed_set(initial, selected)
        } else {
            retired_betree_reclaimed_set(initial, selected).insert(au)
        }).contains(candidate) by {
    }
}

impl BetreeAuBucket {
    pub open spec fn unique_aus(entries: Seq<BetreeAuRecord>) -> bool {
        forall |i: int, j: int|
            #![trigger entries[i].au, entries[j].au]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i].au == entries[j].au
            ==> i == j
    }

    pub open spec fn entries_map(
        entries: Seq<BetreeAuRecord>,
    ) -> Map<AU, SnapshotMembership>
        recommends Self::unique_aus(entries)
    {
        Map::new(
            |au: AU| exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].au as nat == au,
            |au: AU| entries[choose |i: int| #![auto]
                0 <= i < entries.len() && entries[i].au as nat == au].snapshots,
        )
    }

    pub open spec fn wf(&self) -> bool {
        Self::unique_aus(self.entries@)
    }

    proof fn entries_map_index(entries: Seq<BetreeAuRecord>, i: int)
        requires
            Self::unique_aus(entries),
            0 <= i < entries.len(),
        ensures
            Self::entries_map(entries).contains_key(entries[i].au as nat),
            Self::entries_map(entries)[entries[i].au as nat]
                == entries[i].snapshots,
    {
    }

    proof fn entries_map_index_for_au(
        entries: Seq<BetreeAuRecord>,
        au: AU,
    ) -> (i: int)
        requires
            Self::unique_aus(entries),
            Self::entries_map(entries).contains_key(au),
        ensures
            0 <= i < entries.len(),
            entries[i].au as nat == au,
            Self::entries_map(entries)[au] == entries[i].snapshots,
    {
        let i = choose |i: int| #![auto]
            0 <= i < entries.len() && entries[i].au as nat == au;
        Self::entries_map_index(entries, i);
        i
    }

    proof fn entries_map_after_set(
        old_entries: Seq<BetreeAuRecord>,
        index: int,
        entry: BetreeAuRecord,
    )
        requires
            Self::unique_aus(old_entries),
            0 <= index < old_entries.len(),
            old_entries[index].au == entry.au,
        ensures
            Self::unique_aus(old_entries.update(index, entry)),
            Self::entries_map(old_entries.update(index, entry))
                == Self::entries_map(old_entries).insert(
                    entry.au as nat,
                    entry.snapshots,
                ),
    {
        let new_entries = old_entries.update(index, entry);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].au, new_entries[j].au]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].au == new_entries[j].au
            implies i == j by {
            if i != index && j != index {
                assert(new_entries[i] == old_entries[i]);
                assert(new_entries[j] == old_entries[j]);
            } else if i == index && j != index {
                assert(old_entries[index].au == old_entries[j].au);
            } else if i != index && j == index {
                assert(old_entries[i].au == old_entries[index].au);
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(
                entry.au as nat,
                entry.snapshots,
            ),
            au => {
                if au == entry.au as nat {
                    Self::entries_map_index(new_entries, index);
                } else if Self::entries_map(old_entries).contains_key(au) {
                    let i = Self::entries_map_index_for_au(old_entries, au);
                    assert(i != index);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    proof fn entries_map_after_push(
        old_entries: Seq<BetreeAuRecord>,
        entry: BetreeAuRecord,
    )
        requires
            Self::unique_aus(old_entries),
            !Self::entries_map(old_entries).contains_key(entry.au as nat),
        ensures
            Self::unique_aus(old_entries.push(entry)),
            Self::entries_map(old_entries.push(entry))
                == Self::entries_map(old_entries).insert(
                    entry.au as nat,
                    entry.snapshots,
                ),
    {
        let new_entries = old_entries.push(entry);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].au, new_entries[j].au]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].au == new_entries[j].au
            implies i == j by {
            if i < old_entries.len() && j < old_entries.len() {
                assert(new_entries[i] == old_entries[i]);
                assert(new_entries[j] == old_entries[j]);
            } else if i == old_entries.len() && j < old_entries.len() {
                assert(Self::entries_map(old_entries)
                    .contains_key(old_entries[j].au as nat));
            } else if i < old_entries.len() && j == old_entries.len() {
                assert(Self::entries_map(old_entries)
                    .contains_key(old_entries[i].au as nat));
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(
                entry.au as nat,
                entry.snapshots,
            ),
            au => {
                if au == entry.au as nat {
                    Self::entries_map_index(new_entries, old_entries.len() as int);
                } else if Self::entries_map(old_entries).contains_key(au) {
                    let i = Self::entries_map_index_for_au(old_entries, au);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    proof fn entries_map_after_remove(
        old_entries: Seq<BetreeAuRecord>,
        index: int,
    )
        requires
            Self::unique_aus(old_entries),
            0 <= index < old_entries.len(),
        ensures
            Self::unique_aus(old_entries.remove(index)),
            Self::entries_map(old_entries.remove(index))
                == Self::entries_map(old_entries)
                    .remove(old_entries[index].au as nat),
    {
        let new_entries = old_entries.remove(index);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].au, new_entries[j].au]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].au == new_entries[j].au
            implies i == j by {
            let old_i = if i < index { i } else { i + 1 };
            let old_j = if j < index { j } else { j + 1 };
            assert(new_entries[i] == old_entries[old_i]);
            assert(new_entries[j] == old_entries[old_j]);
            assert(old_i == old_j);
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries)
                .remove(old_entries[index].au as nat),
            au => {
                if Self::entries_map(new_entries).contains_key(au) {
                    let i = Self::entries_map_index_for_au(new_entries, au);
                    let old_i = if i < index { i } else { i + 1 };
                    assert(new_entries[i] == old_entries[old_i]);
                    Self::entries_map_index(old_entries, old_i);
                }
                if Self::entries_map(old_entries).contains_key(au)
                    && au != old_entries[index].au as nat
                {
                    let old_i = Self::entries_map_index_for_au(old_entries, au);
                    assert(old_i != index);
                    let i = if old_i < index { old_i } else { old_i - 1 };
                    assert(new_entries[i] == old_entries[old_i]);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    fn new() -> (out: Self)
        ensures
            out.wf(),
            out@ == Map::<AU, SnapshotMembership>::empty(),
            out.entries@.len() == 0,
    {
        let out = Self { entries: Vec::new() };
        assert(out@ == Map::<AU, SnapshotMembership>::empty());
        out
    }

    fn get(&self, au: IAU) -> (out: Option<SnapshotMembership>)
        requires self.wf(),
        ensures
            (out is Some) == self@.contains_key(au as nat),
            out is Some ==> out.unwrap() == self@[au as nat],
    {
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].au != au,
            decreases self.entries.len() - index,
        {
            if self.entries[index].au == au {
                proof {
                    Self::entries_map_index(self.entries@, index as int);
                }
                return Some(self.entries[index].snapshots);
            }
            index += 1;
        }
        proof {
            assert(!self@.contains_key(au as nat)) by {
                if self@.contains_key(au as nat) {
                    let i = Self::entries_map_index_for_au(self.entries@, au as nat);
                    assert(i < index);
                    assert(self.entries@[i].au == au);
                }
            }
        }
        None
    }

    fn set(&mut self, au: IAU, snapshots: Option<SnapshotMembership>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self@ == if snapshots is Some {
                old(self)@.insert(au as nat, snapshots.unwrap())
            } else {
                old(self)@.remove(au as nat)
            },
            forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                ==> self.entries@[i].au == au
                    || exists |old_i: int| #![auto]
                        0 <= old_i < old(self).entries@.len()
                        && old(self).entries@[old_i].au == self.entries@[i].au,
    {
        let ghost old_entries = self.entries@;
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                self.entries@ == old_entries,
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].au != au,
            decreases self.entries.len() - index,
        {
            if self.entries[index].au == au {
                match snapshots {
                    Some(value) => {
                        let entry = BetreeAuRecord { au, snapshots: value };
                        self.entries[index] = entry;
                        proof {
                            assert(self.entries@ == old_entries.update(index as int, entry));
                            Self::entries_map_after_set(old_entries, index as int, entry);
                            assert forall |i: int| #![trigger self.entries@[i]]
                                0 <= i < self.entries@.len()
                                implies self.entries@[i].au == au
                                    || exists |old_i: int| #![auto]
                                        0 <= old_i < old_entries.len()
                                        && old_entries[old_i].au == self.entries@[i].au by {
                                if i != index {
                                    assert(self.entries@[i] == old_entries[i]);
                                }
                            }
                        }
                    },
                    None => {
                        let removed = self.entries.remove(index);
                        proof {
                            assert(removed == old_entries[index as int]);
                            Self::entries_map_after_remove(old_entries, index as int);
                            assert forall |i: int| #![trigger self.entries@[i]]
                                0 <= i < self.entries@.len()
                                implies exists |old_i: int| #![auto]
                                    0 <= old_i < old_entries.len()
                                    && old_entries[old_i].au == self.entries@[i].au by {
                                let old_i = if i < index { i } else { i + 1 };
                                assert(self.entries@[i] == old_entries[old_i]);
                            }
                        }
                    },
                }
                return;
            }
            index += 1;
        }

        match snapshots {
            Some(value) => {
                proof {
                    assert(!Self::entries_map(old_entries).contains_key(au as nat)) by {
                        if Self::entries_map(old_entries).contains_key(au as nat) {
                            let i = Self::entries_map_index_for_au(old_entries, au as nat);
                            assert(i < index);
                            assert(self.entries@[i].au == au);
                        }
                    }
                }
                let entry = BetreeAuRecord { au, snapshots: value };
                self.entries.push(entry);
                proof {
                    Self::entries_map_after_push(old_entries, entry);
                    assert forall |i: int| #![trigger self.entries@[i]]
                        0 <= i < self.entries@.len()
                        implies self.entries@[i].au == au
                            || exists |old_i: int| #![auto]
                                0 <= old_i < old_entries.len()
                                && old_entries[old_i].au == self.entries@[i].au by {
                        if i < old_entries.len() {
                            assert(self.entries@[i] == old_entries[i]);
                        } else {
                            assert(i == old_entries.len());
                        }
                    }
                }
            },
            None => {
                proof {
                    assert(!self@.contains_key(au as nat)) by {
                        if self@.contains_key(au as nat) {
                            let i = Self::entries_map_index_for_au(old_entries, au as nat);
                            assert(i < index);
                            assert(self.entries@[i].au == au);
                        }
                    }
                    assert forall |i: int| #![trigger self.entries@[i]]
                        0 <= i < self.entries@.len()
                        implies exists |old_i: int| #![auto]
                            0 <= old_i < old_entries.len()
                            && old_entries[old_i].au == self.entries@[i].au by {
                        assert(self.entries@[i] == old_entries[i]);
                    }
                }
            },
        }
    }
}

impl View for BetreeAuBucket {
    type V = Map<AU, SnapshotMembership>;

    open spec fn view(&self) -> Self::V {
        Self::entries_map(self.entries@)
    }
}

impl BetreeAuTable {
    pub open spec fn bucket_index(au: AU, bucket_count: nat) -> nat
        recommends bucket_count > 0
    {
        au % bucket_count
    }

    pub open spec fn buckets_map(
        buckets: Seq<BetreeAuBucket>,
        bucket_count: nat,
    ) -> Map<AU, SnapshotMembership>
        recommends
            bucket_count > 0,
            buckets.len() == bucket_count,
            forall |i: int| #![trigger buckets[i]]
                0 <= i < buckets.len() ==> buckets[i].wf(),
    {
        Map::new(
            |au: AU| buckets[Self::bucket_index(au, bucket_count) as int]@
                .contains_key(au),
            |au: AU| buckets[Self::bucket_index(au, bucket_count) as int]@[au],
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.bucket_count > 0
        &&& self.buckets@.len() == self.bucket_count as nat
        &&& forall |bucket: int| #![trigger self.buckets@[bucket]]
            0 <= bucket < self.buckets@.len()
            ==> self.buckets@[bucket].wf()
        &&& forall |bucket: int, entry: int|
            #![trigger self.buckets@[bucket].entries@[entry]]
            0 <= bucket < self.buckets@.len()
            && 0 <= entry < self.buckets@[bucket].entries@.len()
            ==> Self::bucket_index(
                self.buckets@[bucket].entries@[entry].au as nat,
                self.bucket_count as nat,
            ) == bucket
    }

    proof fn view_domain_finite(&self)
        requires self.wf(),
        ensures self@.dom().finite(),
    {
        let int_range = set_int_range(0, u32::MAX as int + 1);
        let executable = Set::<AU>::new(|au: AU| au <= u32::MAX as nat);
        let mapped = int_range.map(|i: int| i as nat);
        lemma_int_range(0, u32::MAX as int + 1);
        int_range.lemma_map_finite(|i: int| i as nat);
        assert(executable =~= mapped) by {
            assert forall |au: AU| #[trigger] executable.contains(au)
                implies mapped.contains(au) by {
                assert(int_range.contains(au as int));
            }
            assert forall |au: AU| #[trigger] mapped.contains(au)
                implies executable.contains(au) by {
                let i = choose |i: int|
                    int_range.contains(i) && i as nat == au;
                assert(0 <= i < u32::MAX as int + 1);
            }
        }
        assert(self@.dom() <= executable) by {
            assert forall |au: AU| #[trigger] self@.dom().contains(au)
                implies executable.contains(au) by {
                let bucket = Self::bucket_index(
                    au,
                    self.bucket_count as nat,
                ) as int;
                assert(self.buckets@[bucket]@.contains_key(au));
                let index = BetreeAuBucket::entries_map_index_for_au(
                    self.buckets@[bucket].entries@,
                    au,
                );
                assert(self.buckets@[bucket].entries@[index].au as nat == au);
            }
        }
        lemma_set_subset_finite(executable, self@.dom());
    }

    pub open spec fn flatten_prefix(
        buckets: Seq<BetreeAuBucket>,
        count: nat,
    ) -> Seq<BetreeAuRecord>
        recommends count <= buckets.len()
        decreases count
    {
        if count == 0 {
            Seq::empty()
        } else {
            Self::flatten_prefix(buckets, (count - 1) as nat)
                + buckets[(count - 1) as int].entries@
        }
    }

    proof fn flatten_prefix_origin(
        buckets: Seq<BetreeAuBucket>,
        count: nat,
        index: int,
    ) -> (origin: (int, int))
        requires
            count <= buckets.len(),
            0 <= index < Self::flatten_prefix(buckets, count).len(),
        ensures
            0 <= origin.0 < count,
            0 <= origin.1 < buckets[origin.0].entries@.len(),
            Self::flatten_prefix(buckets, count)[index]
                == buckets[origin.0].entries@[origin.1],
        decreases count,
    {
        if count == 0 {
            return proof_from_false();
        }
        let prefix = Self::flatten_prefix(buckets, (count - 1) as nat);
        if index < prefix.len() {
            Self::flatten_prefix_origin(buckets, (count - 1) as nat, index)
        } else {
            let entry = index - prefix.len();
            assert(Self::flatten_prefix(buckets, count)[index]
                == buckets[(count - 1) as int].entries@[entry]);
            ((count - 1) as int, entry)
        }
    }

    proof fn flatten_prefix_contains(
        buckets: Seq<BetreeAuBucket>,
        count: nat,
        bucket: int,
        entry: int,
    ) -> (index: int)
        requires
            count <= buckets.len(),
            0 <= bucket < count,
            0 <= entry < buckets[bucket].entries@.len(),
        ensures
            0 <= index < Self::flatten_prefix(buckets, count).len(),
            Self::flatten_prefix(buckets, count)[index]
                == buckets[bucket].entries@[entry],
        decreases count,
    {
        if bucket < count - 1 {
            Self::flatten_prefix_contains(
                buckets,
                (count - 1) as nat,
                bucket,
                entry,
            )
        } else {
            assert(bucket == count - 1);
            let prefix = Self::flatten_prefix(buckets, (count - 1) as nat);
            let index = prefix.len() + entry;
            assert(Self::flatten_prefix(buckets, count)[index]
                == buckets[bucket].entries@[entry]);
            index
        }
    }

    proof fn flatten_prefix_unique(
        buckets: Seq<BetreeAuBucket>,
        count: nat,
        bucket_count: nat,
    )
        requires
            bucket_count > 0,
            count <= buckets.len(),
            forall |bucket: int| #![trigger buckets[bucket]]
                0 <= bucket < count ==> buckets[bucket].wf(),
            forall |bucket: int, entry: int|
                #![trigger buckets[bucket].entries@[entry]]
                0 <= bucket < count
                && 0 <= entry < buckets[bucket].entries@.len()
                ==> Self::bucket_index(
                    buckets[bucket].entries@[entry].au as nat,
                    bucket_count,
                ) == bucket,
        ensures
            BetreeAuBucket::unique_aus(
                Self::flatten_prefix(buckets, count),
            ),
        decreases count,
    {
        if count == 0 {
            return;
        }
        Self::flatten_prefix_unique(
            buckets,
            (count - 1) as nat,
            bucket_count,
        );
        let previous = Self::flatten_prefix(buckets, (count - 1) as nat);
        let current = buckets[(count - 1) as int].entries@;
        let flattened = previous + current;
        assert forall |i: int, j: int|
            #![trigger flattened[i].au, flattened[j].au]
            0 <= i < flattened.len()
            && 0 <= j < flattened.len()
            && flattened[i].au == flattened[j].au
            implies i == j by {
            if i < previous.len() && j < previous.len() {
                assert(previous[i].au == previous[j].au);
            } else if previous.len() <= i && previous.len() <= j {
                let current_i = i - previous.len();
                let current_j = j - previous.len();
                assert(current[current_i].au == current[current_j].au);
                assert(current_i == current_j);
            } else if i < previous.len() && previous.len() <= j {
                let origin = Self::flatten_prefix_origin(
                    buckets,
                    (count - 1) as nat,
                    i,
                );
                let current_j = j - previous.len();
                assert(Self::bucket_index(previous[i].au as nat, bucket_count)
                    == origin.0);
                assert(Self::bucket_index(current[current_j].au as nat, bucket_count)
                    == count - 1);
                assert(origin.0 < count - 1);
            } else {
                let origin = Self::flatten_prefix_origin(
                    buckets,
                    (count - 1) as nat,
                    j,
                );
                let current_i = i - previous.len();
                assert(Self::bucket_index(previous[j].au as nat, bucket_count)
                    == origin.0);
                assert(Self::bucket_index(current[current_i].au as nat, bucket_count)
                    == count - 1);
                assert(origin.0 < count - 1);
            }
        }
    }

    proof fn flatten_represents(&self)
        requires self.wf(),
        ensures
            BetreeAuBucket::unique_aus(Self::flatten_prefix(
                self.buckets@,
                self.buckets@.len(),
            )),
            BetreeAuBucket::entries_map(Self::flatten_prefix(
                self.buckets@,
                self.buckets@.len(),
            )) == self@,
    {
        let flattened = Self::flatten_prefix(
            self.buckets@,
            self.buckets@.len(),
        );
        Self::flatten_prefix_unique(
            self.buckets@,
            self.buckets@.len(),
            self.bucket_count as nat,
        );
        assert_maps_equal!(
            BetreeAuBucket::entries_map(flattened),
            self@,
            au => {
                if BetreeAuBucket::entries_map(flattened).contains_key(au) {
                    let flat_index = BetreeAuBucket::entries_map_index_for_au(
                        flattened,
                        au,
                    );
                    let origin = Self::flatten_prefix_origin(
                        self.buckets@,
                        self.buckets@.len(),
                        flat_index,
                    );
                    let entry = self.buckets@[origin.0].entries@[origin.1];
                    assert(flattened[flat_index] == entry);
                    assert(Self::bucket_index(au, self.bucket_count as nat)
                        == origin.0);
                    BetreeAuBucket::entries_map_index(
                        self.buckets@[origin.0].entries@,
                        origin.1,
                    );
                }
                if self@.contains_key(au) {
                    let bucket = Self::bucket_index(
                        au,
                        self.bucket_count as nat,
                    ) as int;
                    let entry = BetreeAuBucket::entries_map_index_for_au(
                        self.buckets@[bucket].entries@,
                        au,
                    );
                    let flat_index = Self::flatten_prefix_contains(
                        self.buckets@,
                        self.buckets@.len(),
                        bucket,
                        entry,
                    );
                    BetreeAuBucket::entries_map_index(flattened, flat_index);
                }
            }
        );
    }

    fn exec_bucket_index(au: IAU, bucket_count: u32) -> (out: usize)
        requires bucket_count > 0,
        ensures
            out as nat == Self::bucket_index(au as nat, bucket_count as nat),
            out < bucket_count as usize,
    {
        (au % bucket_count) as usize
    }

    fn empty_buckets(bucket_count: u32) -> (out: Vec<BetreeAuBucket>)
        requires bucket_count > 0,
        ensures
            out@.len() == bucket_count as nat,
            forall |i: int| #![trigger out@[i]]
                0 <= i < out@.len()
                ==> out@[i].wf()
                    && out@[i]@ == Map::<AU, SnapshotMembership>::empty()
                    && out@[i].entries@.len() == 0,
    {
        let mut out = Vec::<BetreeAuBucket>::new();
        let mut index = 0usize;
        while index < bucket_count as usize
            invariant
                index <= bucket_count as usize,
                out@.len() == index,
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len()
                    ==> out@[i].wf()
                        && out@[i]@ == Map::<AU, SnapshotMembership>::empty()
                        && out@[i].entries@.len() == 0,
            decreases bucket_count as usize - index,
        {
            out.push(BetreeAuBucket::new());
            index += 1;
        }
        out
    }

    proof fn buckets_update_refines(
        old_buckets: Seq<BetreeAuBucket>,
        new_buckets: Seq<BetreeAuBucket>,
        bucket_count: nat,
        bucket: int,
        au: AU,
        snapshots: Option<SnapshotMembership>,
    )
        requires
            bucket_count > 0,
            old_buckets.len() == bucket_count,
            new_buckets.len() == bucket_count,
            0 <= bucket < old_buckets.len(),
            bucket == Self::bucket_index(au, bucket_count),
            forall |i: int| #![trigger old_buckets[i]]
                0 <= i < old_buckets.len() ==> old_buckets[i].wf(),
            forall |i: int| #![trigger new_buckets[i]]
                0 <= i < new_buckets.len() ==> new_buckets[i].wf(),
            new_buckets[bucket]@ == if snapshots is Some {
                old_buckets[bucket]@.insert(au, snapshots.unwrap())
            } else {
                old_buckets[bucket]@.remove(au)
            },
            forall |i: int| #![trigger new_buckets[i]]
                0 <= i < new_buckets.len() && i != bucket
                ==> new_buckets[i]@ == old_buckets[i]@,
        ensures
            Self::buckets_map(new_buckets, bucket_count) == if snapshots is Some {
                Self::buckets_map(old_buckets, bucket_count)
                    .insert(au, snapshots.unwrap())
            } else {
                Self::buckets_map(old_buckets, bucket_count).remove(au)
            },
    {
        assert_maps_equal!(
            Self::buckets_map(new_buckets, bucket_count),
            if snapshots is Some {
                Self::buckets_map(old_buckets, bucket_count)
                    .insert(au, snapshots.unwrap())
            } else {
                Self::buckets_map(old_buckets, bucket_count).remove(au)
            },
            other_au => {
                let other_bucket = Self::bucket_index(other_au, bucket_count) as int;
                if other_au == au {
                    assert(other_bucket == bucket);
                } else if other_bucket != bucket {
                    assert(new_buckets[other_bucket]@ == old_buckets[other_bucket]@);
                }
            }
        );
    }

    pub fn new(bucket_count: u32) -> (out: Self)
        requires bucket_count > 0,
        ensures
            out.wf(),
            out@ == Map::<AU, SnapshotMembership>::empty(),
            out.bucket_count == bucket_count,
    {
        let buckets = Self::empty_buckets(bucket_count);
        let out = Self { buckets, bucket_count };
        proof {
            assert forall |bucket: int, entry: int|
                #![trigger out.buckets@[bucket].entries@[entry]]
                0 <= bucket < out.buckets@.len()
                && 0 <= entry < out.buckets@[bucket].entries@.len()
                implies Self::bucket_index(
                    out.buckets@[bucket].entries@[entry].au as nat,
                    out.bucket_count as nat,
                ) == bucket by {
                assert(out.buckets@[bucket].entries@.len() == 0);
            }
            assert(out.wf());
            assert_maps_equal!(out@, Map::<AU, SnapshotMembership>::empty(), au => {});
        }
        out
    }

    pub fn get(&self, au: IAU) -> (out: Option<SnapshotMembership>)
        requires self.wf(),
        ensures
            (out is Some) == self@.contains_key(au as nat),
            out is Some ==> out.unwrap() == self@[au as nat],
    {
        let bucket = Self::exec_bucket_index(au, self.bucket_count);
        self.buckets[bucket].get(au)
    }

    fn set(&mut self, au: IAU, snapshots: Option<SnapshotMembership>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            self@ == if snapshots is Some {
                old(self)@.insert(au as nat, snapshots.unwrap())
            } else {
                old(self)@.remove(au as nat)
            },
    {
        let bucket = Self::exec_bucket_index(au, self.bucket_count);
        let ghost old_buckets = self.buckets@;
        let mut selected = self.buckets.remove(bucket);
        selected.set(au, snapshots);
        self.buckets.insert(bucket, selected);
        proof {
            assert forall |i: int| #![trigger self.buckets@[i]]
                0 <= i < self.buckets@.len()
                implies self.buckets@[i].wf() by {
                if i != bucket {
                    assert(self.buckets@[i] == old_buckets[i]);
                }
            }
            assert forall |b: int, e: int|
                #![trigger self.buckets@[b].entries@[e]]
                0 <= b < self.buckets@.len()
                && 0 <= e < self.buckets@[b].entries@.len()
                implies Self::bucket_index(
                    self.buckets@[b].entries@[e].au as nat,
                    self.bucket_count as nat,
                ) == b by {
                if b == bucket {
                    let record = self.buckets@[b].entries@[e];
                    assert(record.au == au || exists |old_i: int| #![auto]
                        0 <= old_i < old_buckets[b].entries@.len()
                        && old_buckets[b].entries@[old_i].au == record.au);
                    if record.au == au {
                        assert(Self::bucket_index(
                            record.au as nat,
                            self.bucket_count as nat,
                        ) == bucket);
                    } else {
                        let old_i = choose |old_i: int| #![auto]
                            0 <= old_i < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_i].au == record.au;
                        assert(Self::bucket_index(
                            old_buckets[b].entries@[old_i].au as nat,
                            self.bucket_count as nat,
                        ) == b);
                    }
                } else {
                    assert(self.buckets@[b] == old_buckets[b]);
                }
            }
            assert(self.wf());
            Self::buckets_update_refines(
                old_buckets,
                self.buckets@,
                self.bucket_count as nat,
                bucket as int,
                au as nat,
                snapshots,
            );
        }
    }

    pub fn flatten(&self) -> (out: Vec<BetreeAuRecord>)
        requires self.wf(),
        ensures
            BetreeAuBucket::unique_aus(out@),
            BetreeAuBucket::entries_map(out@) == self@,
            out@ == Self::flatten_prefix(self.buckets@, self.buckets@.len()),
    {
        let mut out = Vec::<BetreeAuRecord>::new();
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                bucket <= self.buckets.len(),
                out@ == Self::flatten_prefix(self.buckets@, bucket as nat),
            decreases self.buckets.len() - bucket,
        {
            let mut entry = 0usize;
            let bucket_len = self.buckets[bucket].entries.len();
            while entry < bucket_len
                invariant
                    self.wf(),
                    bucket < self.buckets.len(),
                    bucket_len == self.buckets@[bucket as int].entries@.len(),
                    entry <= bucket_len,
                    out@ == Self::flatten_prefix(self.buckets@, bucket as nat)
                        + self.buckets@[bucket as int].entries@
                            .subrange(0, entry as int),
                decreases bucket_len - entry,
            {
                out.push(self.buckets[bucket].entries[entry]);
                entry += 1;
            }
            proof {
                assert(self.buckets@[bucket as int].entries@
                    .subrange(0, entry as int)
                    == self.buckets@[bucket as int].entries@);
                assert(Self::flatten_prefix(self.buckets@, bucket as nat + 1)
                    == Self::flatten_prefix(self.buckets@, bucket as nat)
                        + self.buckets@[bucket as int].entries@);
            }
            bucket += 1;
        }
        proof {
            self.flatten_represents();
        }
        out
    }
}

impl View for BetreeAuTable {
    type V = Map<AU, SnapshotMembership>;

    open spec fn view(&self) -> Self::V {
        Self::buckets_map(self.buckets@, self.bucket_count as nat)
    }
}

impl BetreeAuOwnershipImpl {
    pub open spec fn wf(&self) -> bool {
        &&& self.active.wf()
        &&& self.retired.wf()
        &&& self.active.bucket_count == self.retired.bucket_count
        &&& self.active@.dom().disjoint(self.retired@.dom())
        &&& forall |au: AU| #[trigger] self.retired@.contains_key(au)
            ==> self.retired@[au].protected()
    }

    pub open spec fn active_aus(&self) -> Set<AU> {
        self.active@.dom()
    }

    pub open spec fn all_aus(&self) -> Set<AU> {
        self.active@.dom() + self.retired@.dom()
    }

    pub open spec fn persistent_aus(&self) -> Set<AU> {
        Set::new(|au: AU|
            (self.active@.contains_key(au) && self.active@[au].persistent)
            || (self.retired@.contains_key(au) && self.retired@[au].persistent))
    }

    pub open spec fn frozen_aus(&self) -> Set<AU> {
        Set::new(|au: AU|
            (self.active@.contains_key(au) && self.active@[au].frozen)
            || (self.retired@.contains_key(au) && self.retired@[au].frozen))
    }

    pub proof fn ownership_sets_bounded(&self)
        requires self.wf(),
        ensures
            self.active_aus() <= self.all_aus(),
            self.persistent_aus() <= self.all_aus(),
            self.frozen_aus() <= self.all_aus(),
    {
        assert forall |au: AU| #[trigger] self.active_aus().contains(au)
            implies self.all_aus().contains(au) by { }
        assert forall |au: AU| #[trigger] self.persistent_aus().contains(au)
            implies self.all_aus().contains(au) by { }
        assert forall |au: AU| #[trigger] self.frozen_aus().contains(au)
            implies self.all_aus().contains(au) by { }
    }

    pub proof fn view_domain_matches_active(&self)
        requires self.wf(),
        ensures self@.dom() =~= self.active_aus(),
    {
        self.active.view_domain_finite();
        let counts = Map::new(
            |au: AU| self.active_aus().contains(au),
            |au: AU| 1nat,
        );
        assert(counts.dom() =~= self.active_aus()) by {
            assert forall |au: AU| #[trigger] counts.dom().contains(au)
                == self.active_aus().contains(au) by {}
        }
        assert(counts.dom().finite());
        broadcast use vstd::multiset::group_multiset_axioms;
        assert forall |au: AU| #[trigger] self@.dom().contains(au)
            == self.active_aus().contains(au) by {
            if counts.dom().contains(au) {
                assert(self@.count(au) == counts[au]);
            } else {
                assert(self@.count(au) == 0);
            }
        }
    }

    pub proof fn view_count_matches_active(&self, au: AU)
        requires self.wf(),
        ensures self@.count(au) == if self.active_aus().contains(au) {
            1nat
        } else {
            0nat
        },
    {
        self.active.view_domain_finite();
        let counts = Map::new(
            |candidate: AU| self.active_aus().contains(candidate),
            |candidate: AU| 1nat,
        );
        assert(counts.dom() =~= self.active_aus()) by {
            assert forall |candidate: AU|
                #[trigger] counts.dom().contains(candidate)
                == self.active_aus().contains(candidate) by {}
        }
        assert(counts.dom().finite());
        if counts.dom().contains(au) {
            assert(self@.count(au) == counts[au]);
        } else {
            assert(self@.count(au) == 0);
        }
    }

    pub open spec fn count_one_likes(&self) -> AULikes {
        AULikes::from_map(Map::new(
            |au: AU| self.active_aus().contains(au),
            |au: AU| 1nat,
        ))
    }

    pub fn new(bucket_count: u32) -> (out: Self)
        requires bucket_count > 0,
        ensures
            out.wf(),
            out.active.bucket_count == bucket_count,
            out.retired.bucket_count == bucket_count,
            out@ == AULikes::empty(),
            out.active_aus() == Set::<AU>::empty(),
            out.all_aus() == Set::<AU>::empty(),
            out.persistent_aus() == Set::<AU>::empty(),
            out.frozen_aus() == Set::<AU>::empty(),
    {
        let active = BetreeAuTable::new(bucket_count);
        let retired = BetreeAuTable::new(bucket_count);
        let out = Self { active, retired };
        proof {
            assert(out.wf());
            assert(out.active_aus() == Set::<AU>::empty());
            let counts = Map::new(
                |au: AU| out.active_aus().contains(au),
                |au: AU| 1nat,
            );
            assert(counts.dom() =~= Set::<AU>::empty()) by {
                assert forall |au: AU| #[trigger] counts.dom().contains(au)
                    == out.active_aus().contains(au) by { }
            }
            assert(counts.dom().finite());
            broadcast use vstd::multiset::group_multiset_axioms;
            assert_multisets_equal!(out@, AULikes::empty(), au => {
                assert(!counts.dom().contains(au));
            });
            assert(out.all_aus() == Set::<AU>::empty());
            assert(out.persistent_aus() == Set::<AU>::empty());
            assert(out.frozen_aus() == Set::<AU>::empty());
        }
        out
    }

    pub fn contains_active(&self, au: IAU) -> (out: bool)
        requires self.wf(),
        ensures out == self.active_aus().contains(au as nat),
    {
        self.active.get(au).is_some()
    }

    pub fn contains_owned_au(&self, au: IAU) -> (out: bool)
        requires self.wf(),
        ensures out == self.all_aus().contains(au as nat),
    {
        let active = self.active.get(au).is_some();
        let retired = self.retired.get(au).is_some();
        active || retired
    }

    pub fn allocate(&mut self, au: IAU) -> (result: BetreeOwnershipUpdateResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==>
                !old(self).active@.contains_key(au as nat)
                && !old(self).retired@.contains_key(au as nat),
            match result {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.active@ == old(self).active@.insert(
                        au as nat,
                        SnapshotMembership {
                            persistent: false,
                            frozen: false,
                        },
                    )
                    &&& self.retired@ == old(self).retired@
                    &&& self@ == old(self)@.insert(au as nat)
                    &&& self.active_aus() =~= old(self).active_aus().insert(au as nat)
                    &&& self.all_aus() =~= old(self).all_aus().insert(au as nat)
                    &&& self.persistent_aus() =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BetreeOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                    &&& self.active.bucket_count == old(self).active.bucket_count
                    &&& self.retired.bucket_count == old(self).retired.bucket_count
                },
            },
    {
        let active = self.active.get(au);
        let retired = self.retired.get(au);
        if active.is_some() || retired.is_some() {
            return BetreeOwnershipUpdateResult::Noop;
        }
        let snapshots = SnapshotMembership::ephemeral();
        self.active.set(au, Some(snapshots));
        proof {
            assert(!old(self).active@.contains_key(au as nat));
            assert(!old(self).retired@.contains_key(au as nat));
            assert(self.active@.contains_key(au as nat));
            assert(self.active@[au as nat].unprotected());
            assert(self.wf());
            assert(self.persistent_aus() =~= old(self).persistent_aus()) by {
                assert forall |other: AU| #![trigger self.persistent_aus().contains(other)]
                    self.persistent_aus().contains(other)
                    == old(self).persistent_aus().contains(other) by {
                    if other == au as nat {
                    } else {
                        assert(self.active@.contains_key(other)
                            == old(self).active@.contains_key(other));
                        if self.active@.contains_key(other) {
                            assert(self.active@[other] == old(self).active@[other]);
                        }
                    }
                }
            }
            assert(self.frozen_aus() =~= old(self).frozen_aus()) by {
                assert forall |other: AU| #![trigger self.frozen_aus().contains(other)]
                    self.frozen_aus().contains(other)
                    == old(self).frozen_aus().contains(other) by {
                    if other == au as nat {
                    } else {
                        assert(self.active@.contains_key(other)
                            == old(self).active@.contains_key(other));
                        if self.active@.contains_key(other) {
                            assert(self.active@[other] == old(self).active@[other]);
                        }
                    }
                }
            }
            let new_counts = Map::new(
                |candidate: AU| self.active_aus().contains(candidate),
                |candidate: AU| 1nat,
            );
            let old_counts = Map::new(
                |candidate: AU| old(self).active_aus().contains(candidate),
                |candidate: AU| 1nat,
            );
            assert(new_counts.dom() =~= self.active_aus()) by {
                assert forall |candidate: AU|
                    #[trigger] new_counts.dom().contains(candidate)
                    == self.active_aus().contains(candidate) by {}
            }
            assert(old_counts.dom() =~= old(self).active_aus()) by {
                assert forall |candidate: AU|
                    #[trigger] old_counts.dom().contains(candidate)
                    == old(self).active_aus().contains(candidate) by {}
            }
            self.active.view_domain_finite();
            old(self).active.view_domain_finite();
            assert(new_counts.dom().finite());
            assert(old_counts.dom().finite());
            broadcast use vstd::multiset::group_multiset_axioms;
            assert_multisets_equal!(self@, old(self)@.insert(au as nat), candidate => {
                if candidate == au as nat {
                    assert(self.active_aus().contains(candidate));
                    assert(!old(self).active_aus().contains(candidate));
                    assert(new_counts.dom().contains(candidate));
                    assert(!old_counts.dom().contains(candidate));
                } else {
                    assert(self.active_aus().contains(candidate)
                        == old(self).active_aus().contains(candidate));
                    assert(new_counts.dom().contains(candidate)
                        == old_counts.dom().contains(candidate));
                }
            });
        }
        BetreeOwnershipUpdateResult::Applied { reclaimed: Vec::new() }
    }

    pub fn install_recovered(
        &mut self,
        aus: &Vec<IAU>,
    ) -> (result: BetreeOwnershipUpdateResult)
        requires
            old(self).wf(),
            unique_iau_seq(aus@),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==>
                old(self).active_aus().disjoint(iau_seq_set(aus@))
                && old(self).retired@.dom().disjoint(iau_seq_set(aus@)),
            match result {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.active_aus()
                        =~= old(self).active_aus() + iau_seq_set(aus@)
                    &&& self.all_aus()
                        =~= old(self).all_aus() + iau_seq_set(aus@)
                    &&& self.persistent_aus()
                        =~= old(self).persistent_aus() + iau_seq_set(aus@)
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BetreeOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                    &&& self.active.bucket_count == old(self).active.bucket_count
                    &&& self.retired.bucket_count == old(self).retired.bucket_count
                },
            },
    {
        let active_bucket_count = self.active.bucket_count;
        let retired_bucket_count = self.retired.bucket_count;
        let mut check = 0usize;
        while check < aus.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                self.active.buckets@ == old(self).active.buckets@,
                self.retired.buckets@ == old(self).retired.buckets@,
                check <= aus.len(),
                forall |i: int| #![trigger aus@[i]]
                    0 <= i < check
                    ==> !self.active@.contains_key(aus@[i] as nat)
                        && !self.retired@.contains_key(aus@[i] as nat),
            decreases aus.len() - check,
        {
            if self.active.get(aus[check]).is_some()
                || self.retired.get(aus[check]).is_some()
            {
                return BetreeOwnershipUpdateResult::Noop;
            }
            check += 1;
        }

        let recovered = SnapshotMembership::recovered();
        let ghost initial_active = self.active@;
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();
        let mut index = 0usize;
        while index < aus.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                index <= aus.len(),
                self.retired@ == old(self).retired@,
                self.active@.dom()
                    =~= initial_active.dom() + iau_seq_set(aus@.take(index as int)),
                self.persistent_aus()
                    =~= initial_persistent + iau_seq_set(aus@.take(index as int)),
                self.frozen_aus() =~= initial_frozen,
            decreases aus.len() - index,
        {
            let au = aus[index];
            proof {
                assert(!self.active@.contains_key(au as nat)) by {
                    if initial_active.contains_key(au as nat) {
                        assert(old(self).active@.contains_key(au as nat));
                    } else if iau_seq_set(aus@.take(index as int)).contains(au as nat) {
                        let earlier = choose |i: int| #![auto]
                            0 <= i < aus@.take(index as int).len()
                            && aus@.take(index as int)[i] as nat == au as nat;
                        assert(aus@[earlier] == au);
                        assert(earlier != index);
                    }
                }
            }
            let ghost before_active = self.active@;
            let ghost before_active_aus = self.active_aus();
            let ghost before_persistent = self.persistent_aus();
            let ghost before_frozen = self.frozen_aus();
            self.active.set(au, Some(recovered));
            proof {
                assert(self.active_aus()
                    =~= before_active_aus.insert(au as nat)) by {
                    assert forall |candidate: AU|
                        #![trigger self.active_aus().contains(candidate)]
                        self.active_aus().contains(candidate)
                        == before_active_aus.insert(au as nat).contains(candidate) by {
                    }
                }
                assert(aus@.take(index as int + 1)
                    == aus@.take(index as int).push(au));
                iau_seq_set_push(aus@.take(index as int), au);
                assert(self.persistent_aus()
                    =~= before_persistent.insert(au as nat)) by {
                    assert forall |candidate: AU| #![trigger
                        self.persistent_aus().contains(candidate)]
                        self.persistent_aus().contains(candidate)
                        == before_persistent.insert(au as nat).contains(candidate) by {
                        if candidate == au as nat {
                        } else {
                            assert(self.active@.contains_key(candidate)
                                == before_active.contains_key(candidate));
                            if self.active@.contains_key(candidate) {
                                assert(self.active@[candidate] == before_active[candidate]);
                            }
                        }
                    }
                }
                assert(self.frozen_aus() =~= before_frozen) by {
                    assert forall |candidate: AU| #![trigger
                        self.frozen_aus().contains(candidate)]
                        self.frozen_aus().contains(candidate)
                        == initial_frozen.contains(candidate) by {
                        if candidate != au as nat {
                            assert(self.active@.contains_key(candidate)
                                == before_active.contains_key(candidate));
                            if self.active@.contains_key(candidate) {
                                assert(self.active@[candidate] == before_active[candidate]);
                            }
                        }
                    }
                }
                assert(before_active_aus
                    =~= initial_active.dom()
                        + iau_seq_set(aus@.take(index as int)));
                assert(before_persistent
                    =~= initial_persistent
                        + iau_seq_set(aus@.take(index as int)));
                assert(before_frozen =~= initial_frozen);
                assert(self.active_aus()
                    =~= initial_active.dom()
                        + iau_seq_set(aus@.take(index as int + 1)));
                assert(self.persistent_aus()
                    =~= initial_persistent
                        + iau_seq_set(aus@.take(index as int + 1)));
                assert(self.frozen_aus() =~= initial_frozen);
            }
            index += 1;
        }
        proof {
            assert(self.active.bucket_count == active_bucket_count);
            assert(self.retired.bucket_count == retired_bucket_count);
            assert(aus@.take(index as int) == aus@);
            assert(initial_active == old(self).active@);
            assert(initial_persistent =~= old(self).persistent_aus());
            assert(initial_frozen =~= old(self).frozen_aus());
            assert(self.active_aus()
                =~= old(self).active_aus() + iau_seq_set(aus@));
        }
        BetreeOwnershipUpdateResult::Applied { reclaimed: Vec::new() }
    }

    pub fn retire(
        &mut self,
        au: IAU,
    ) -> (result: BetreeOwnershipUpdateResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==> old(self).active@.contains_key(au as nat),
            match result {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& self.active_aus() =~= old(self).active_aus().remove(au as nat)
                    &&& self.all_aus()
                        =~= if old(self).active@[au as nat].unprotected() {
                            old(self).all_aus().remove(au as nat)
                        } else {
                            old(self).all_aus()
                        }
                    &&& iau_seq_set(reclaimed@)
                        =~= if old(self).active@[au as nat].unprotected() {
                            set![au as nat]
                        } else {
                            Set::<AU>::empty()
                        }
                    &&& unique_iau_seq(reclaimed@)
                    &&& self.persistent_aus() =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BetreeOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                    &&& self.active.bucket_count == old(self).active.bucket_count
                    &&& self.retired.bucket_count == old(self).retired.bucket_count
                },
            },
    {
        let snapshots = self.active.get(au);
        if snapshots.is_none() {
            return BetreeOwnershipUpdateResult::Noop;
        }
        let snapshots = snapshots.unwrap();
        self.active.set(au, None);
        if snapshots.persistent || snapshots.frozen {
            self.retired.set(au, Some(snapshots));
            proof {
                assert(self.wf());
                assert(self.persistent_aus() =~= old(self).persistent_aus());
                assert(self.frozen_aus() =~= old(self).frozen_aus());
            }
            BetreeOwnershipUpdateResult::Applied { reclaimed: Vec::new() }
        } else {
            let mut reclaimed = Vec::<IAU>::new();
            reclaimed.push(au);
            proof {
                assert(self.wf());
                iau_seq_set_singleton(au);
                assert(iau_seq_set(reclaimed@) =~= set![au as nat]);
                assert(unique_iau_seq(reclaimed@));
                assert(self.persistent_aus() =~= old(self).persistent_aus());
                assert(self.frozen_aus() =~= old(self).frozen_aus());
            }
            BetreeOwnershipUpdateResult::Applied { reclaimed }
        }
    }

    pub fn freeze_current(&mut self)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            self.all_aus() =~= old(self).all_aus(),
            self.active_aus() =~= old(self).active_aus(),
            self.persistent_aus() =~= old(self).persistent_aus(),
            self.frozen_aus()
                =~= old(self).frozen_aus() + old(self).active_aus(),
    {
        let active_bucket_count = self.active.bucket_count;
        let retired_bucket_count = self.retired.bucket_count;
        let records = self.active.flatten();
        let ghost initial_active = self.active@;
        let ghost initial_retired = self.retired@;
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();
        let mut index = 0usize;
        while index < records.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                BetreeAuBucket::unique_aus(records@),
                BetreeAuBucket::entries_map(records@) == initial_active,
                index <= records.len(),
                self.retired@ == initial_retired,
                self.active@
                    == freeze_betree_selected(
                        initial_active,
                        BetreeAuBucket::entries_map(
                            records@.take(index as int),
                        ).dom(),
                    ),
                self.active@.dom() == initial_active.dom(),
                self.persistent_aus() =~= initial_persistent,
                self.frozen_aus()
                    =~= initial_frozen
                        + BetreeAuBucket::entries_map(
                            records@.take(index as int),
                        ).dom(),
            decreases records.len() - index,
        {
            let record = records[index];
            let ghost prefix = records@.take(index as int);
            let ghost selected = BetreeAuBucket::entries_map(prefix).dom();
            proof {
                BetreeAuBucket::entries_map_index(records@, index as int);
                assert(initial_active.contains_key(record.au as nat));
                assert(initial_active[record.au as nat] == record.snapshots);
                assert(!selected.contains(record.au as nat)) by {
                    if selected.contains(record.au as nat) {
                        let earlier = BetreeAuBucket::entries_map_index_for_au(
                            prefix,
                            record.au as nat,
                        );
                        assert(records@[earlier].au == record.au);
                        assert(earlier != index);
                    }
                }
            }
            let mut snapshots = record.snapshots;
            snapshots.mark_frozen();
            self.active.set(record.au, Some(snapshots));
            proof {
                freeze_selected_insert(
                    initial_active,
                    selected,
                    record.au as nat,
                );
                assert(records@.take(index as int + 1)
                    == prefix.push(record));
                BetreeAuBucket::entries_map_after_push(prefix, record);
                assert(self.active@
                    == freeze_betree_selected(
                        initial_active,
                        BetreeAuBucket::entries_map(
                            records@.take(index as int + 1),
                        ).dom(),
                    ));
                assert(self.active@.dom() == initial_active.dom());
                assert(self.wf());
                assert(self.persistent_aus() =~= initial_persistent) by {
                    assert forall |au: AU|
                        #![trigger self.persistent_aus().contains(au)]
                        self.persistent_aus().contains(au)
                        == initial_persistent.contains(au) by {
                    }
                }
                assert(self.frozen_aus()
                    =~= initial_frozen
                        + BetreeAuBucket::entries_map(
                            records@.take(index as int + 1),
                        ).dom()) by {
                    assert forall |au: AU|
                        #![trigger self.frozen_aus().contains(au)]
                        self.frozen_aus().contains(au)
                        == (initial_frozen
                            + BetreeAuBucket::entries_map(
                                records@.take(index as int + 1),
                            ).dom()).contains(au) by {
                    }
                }
            }
            index += 1;
        }
        proof {
            assert(self.active.bucket_count == active_bucket_count);
            assert(self.retired.bucket_count == retired_bucket_count);
            assert(records@.take(index as int) == records@);
            assert(BetreeAuBucket::entries_map(records@).dom()
                == initial_active.dom());
            assert(initial_active == old(self).active@);
            assert(initial_retired == old(self).retired@);
            assert(initial_persistent =~= old(self).persistent_aus());
            assert(initial_frozen =~= old(self).frozen_aus());
        }
    }
}

impl BetreeAuOwnershipImpl {
    pub fn commit_complete(&mut self) -> (reclaimed: Vec<IAU>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            self.all_aus() <= old(self).all_aus(),
            self.active_aus() =~= old(self).active_aus(),
            self.persistent_aus() =~= old(self).frozen_aus(),
            self.frozen_aus() =~= Set::<AU>::empty(),
            unique_iau_seq(reclaimed@),
            iau_seq_set(reclaimed@)
                =~= old(self).persistent_aus()
                    - old(self).frozen_aus()
                    - old(self).active_aus(),
    {
        let active_bucket_count = self.active.bucket_count;
        let retired_bucket_count = self.retired.bucket_count;
        let active_records = self.active.flatten();
        let retired_records = self.retired.flatten();
        let ghost initial_active = self.active@;
        let ghost initial_retired = self.retired@;
        let ghost initial_active_aus = self.active_aus();
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();

        let mut active_index = 0usize;
        while active_index < active_records.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                BetreeAuBucket::unique_aus(active_records@),
                BetreeAuBucket::entries_map(active_records@) == initial_active,
                active_index <= active_records.len(),
                self.retired@ == initial_retired,
                self.active@
                    == commit_active_betree_selected(
                        initial_active,
                        BetreeAuBucket::entries_map(
                            active_records@.take(active_index as int),
                        ).dom(),
                    ),
                self.active@.dom() == initial_active.dom(),
            decreases active_records.len() - active_index,
        {
            let record = active_records[active_index];
            let ghost prefix = active_records@.take(active_index as int);
            let ghost selected = BetreeAuBucket::entries_map(prefix).dom();
            proof {
                BetreeAuBucket::entries_map_index(
                    active_records@,
                    active_index as int,
                );
                assert(initial_active.contains_key(record.au as nat));
                assert(initial_active[record.au as nat] == record.snapshots);
                assert(!selected.contains(record.au as nat)) by {
                    if selected.contains(record.au as nat) {
                        let earlier = BetreeAuBucket::entries_map_index_for_au(
                            prefix,
                            record.au as nat,
                        );
                        assert(active_records@[earlier].au == record.au);
                        assert(earlier != active_index);
                    }
                }
            }
            let mut snapshots = record.snapshots;
            snapshots.finish_commit();
            self.active.set(record.au, Some(snapshots));
            proof {
                commit_active_selected_insert(
                    initial_active,
                    selected,
                    record.au as nat,
                );
                assert(active_records@.take(active_index as int + 1)
                    == prefix.push(record));
                BetreeAuBucket::entries_map_after_push(prefix, record);
                assert(self.active@
                    == commit_active_betree_selected(
                        initial_active,
                        BetreeAuBucket::entries_map(
                            active_records@.take(active_index as int + 1),
                        ).dom(),
                    ));
                assert(self.active@.dom() == initial_active.dom());
                assert(self.wf());
            }
            active_index += 1;
        }

        let ghost committed_active = self.active@;
        let mut reclaimed = Vec::<IAU>::new();
        let mut retired_index = 0usize;
        while retired_index < retired_records.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                BetreeAuBucket::unique_aus(retired_records@),
                BetreeAuBucket::entries_map(retired_records@) == initial_retired,
                retired_index <= retired_records.len(),
                self.active@ == committed_active,
                self.retired@
                    == commit_retired_betree_selected(
                        initial_retired,
                        BetreeAuBucket::entries_map(
                            retired_records@.take(retired_index as int),
                        ).dom(),
                    ),
                unique_iau_seq(reclaimed@),
                iau_seq_set(reclaimed@)
                    =~= retired_betree_reclaimed_set(
                        initial_retired,
                        BetreeAuBucket::entries_map(
                            retired_records@.take(retired_index as int),
                        ).dom(),
                    ),
            decreases retired_records.len() - retired_index,
        {
            let record = retired_records[retired_index];
            let ghost prefix = retired_records@.take(retired_index as int);
            let ghost selected = BetreeAuBucket::entries_map(prefix).dom();
            let ghost before_reclaimed = reclaimed@;
            let ghost before_reclaimed_set = iau_seq_set(reclaimed@);
            proof {
                BetreeAuBucket::entries_map_index(
                    retired_records@,
                    retired_index as int,
                );
                assert(initial_retired.contains_key(record.au as nat));
                assert(initial_retired[record.au as nat] == record.snapshots);
                assert(!selected.contains(record.au as nat)) by {
                    if selected.contains(record.au as nat) {
                        let earlier = BetreeAuBucket::entries_map_index_for_au(
                            prefix,
                            record.au as nat,
                        );
                        assert(retired_records@[earlier].au == record.au);
                        assert(earlier != retired_index);
                    }
                }
            }
            if record.snapshots.frozen {
                let mut snapshots = record.snapshots;
                snapshots.finish_commit();
                self.retired.set(record.au, Some(snapshots));
            } else {
                self.retired.set(record.au, None);
                proof {
                    assert(!iau_seq_set(reclaimed@).contains(record.au as nat)) by {
                        if iau_seq_set(reclaimed@).contains(record.au as nat) {
                            assert(retired_betree_reclaimed_set(
                                initial_retired,
                                selected,
                            ).contains(record.au as nat));
                            assert(selected.contains(record.au as nat));
                        }
                    }
                }
                reclaimed.push(record.au);
                proof {
                    assert(reclaimed@ == before_reclaimed.push(record.au));
                    iau_seq_set_push(before_reclaimed, record.au);
                    assert(iau_seq_set(reclaimed@)
                        =~= before_reclaimed_set.insert(record.au as nat));
                    assert(unique_iau_seq(reclaimed@));
                }
            }
            proof {
                commit_retired_selected_insert(
                    initial_retired,
                    selected,
                    record.au as nat,
                );
                assert(retired_records@.take(retired_index as int + 1)
                    == prefix.push(record));
                BetreeAuBucket::entries_map_after_push(prefix, record);
                assert(self.retired@
                    == commit_retired_betree_selected(
                        initial_retired,
                        BetreeAuBucket::entries_map(
                            retired_records@.take(retired_index as int + 1),
                        ).dom(),
                    ));
                assert(before_reclaimed_set
                    =~= retired_betree_reclaimed_set(
                        initial_retired,
                        selected,
                    ));
                assert(iau_seq_set(reclaimed@)
                    =~= if record.snapshots.frozen {
                        before_reclaimed_set
                    } else {
                        before_reclaimed_set.insert(record.au as nat)
                    });
                assert(iau_seq_set(reclaimed@)
                    =~= retired_betree_reclaimed_set(
                        initial_retired,
                        BetreeAuBucket::entries_map(
                            retired_records@.take(retired_index as int + 1),
                        ).dom(),
                    ));
                assert(self.wf());
            }
            retired_index += 1;
        }
        proof {
            assert(active_records@.take(active_index as int) == active_records@);
            assert(retired_records@.take(retired_index as int) == retired_records@);
            assert(BetreeAuBucket::entries_map(active_records@).dom()
                == initial_active.dom());
            assert(BetreeAuBucket::entries_map(retired_records@).dom()
                == initial_retired.dom());
            assert(self.active_aus() =~= initial_active_aus);
            assert(self.persistent_aus() =~= initial_frozen) by {
                assert forall |au: AU|
                    #![trigger self.persistent_aus().contains(au)]
                    self.persistent_aus().contains(au)
                    == initial_frozen.contains(au) by {
                }
            }
            assert(self.frozen_aus() =~= Set::<AU>::empty()) by {
                assert forall |au: AU|
                    #![trigger self.frozen_aus().contains(au)]
                    !self.frozen_aus().contains(au) by {
                }
            }
            assert(iau_seq_set(reclaimed@)
                =~= initial_persistent - initial_frozen - initial_active_aus) by {
                assert forall |au: AU|
                    #![trigger iau_seq_set(reclaimed@).contains(au)]
                    iau_seq_set(reclaimed@).contains(au)
                    == (initial_persistent - initial_frozen - initial_active_aus)
                        .contains(au) by {
                    if initial_retired.contains_key(au) {
                        assert(initial_retired[au].protected());
                    }
                }
            }
            assert(initial_active == old(self).active@);
            assert(initial_retired == old(self).retired@);
            assert(initial_active_aus =~= old(self).active_aus());
            assert(initial_persistent =~= old(self).persistent_aus());
            assert(initial_frozen =~= old(self).frozen_aus());
        }
        proof {
            assert(self.active.bucket_count == active_bucket_count);
            assert(self.retired.bucket_count == retired_bucket_count);
        }
        reclaimed
    }
}

impl View for BetreeAuOwnershipImpl {
    type V = AULikes;

    open spec fn view(&self) -> Self::V {
        self.count_one_likes()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BranchSummaryHeader {
    pub root_au: IAU,
    pub snapshots: SnapshotMembership,
}

#[verifier::ext_equal]
pub struct BranchSummaryRecordView {
    pub summary: Summary,
    pub snapshots: SnapshotMembership,
}

pub struct BranchSummaryBucket {
    pub entries: Vec<BranchSummaryRecord>,
}

pub struct BranchSummaryTable {
    pub buckets: Vec<BranchSummaryBucket>,
    pub bucket_count: u32,
}

pub struct BranchSummaryOwnershipImpl {
    pub active: BranchSummaryTable,
    pub retired: BranchSummaryTable,
}

pub open spec fn freeze_branch_selected(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
) -> Map<AU, BranchSummaryRecordView> {
    Map::new(
        |root: AU| initial.contains_key(root),
        |root: AU| BranchSummaryRecordView {
            summary: initial[root].summary,
            snapshots: if selected.contains(root) {
                initial[root].snapshots.freeze()
            } else {
                initial[root].snapshots
            },
        },
    )
}

pub open spec fn commit_active_branch_selected(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
) -> Map<AU, BranchSummaryRecordView> {
    Map::new(
        |root: AU| initial.contains_key(root),
        |root: AU| BranchSummaryRecordView {
            summary: initial[root].summary,
            snapshots: if selected.contains(root) {
                initial[root].snapshots.commit_complete()
            } else {
                initial[root].snapshots
            },
        },
    )
}

pub open spec fn commit_retired_branch_selected(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
) -> Map<AU, BranchSummaryRecordView> {
    Map::new(
        |root: AU| initial.contains_key(root)
            && (!selected.contains(root) || initial[root].snapshots.frozen),
        |root: AU| BranchSummaryRecordView {
            summary: initial[root].summary,
            snapshots: if selected.contains(root) {
                initial[root].snapshots.commit_complete()
            } else {
                initial[root].snapshots
            },
        },
    )
}

pub open spec fn retired_branch_reclaimed_set(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
) -> Set<AU> {
    Set::new(|au: AU| exists |root: AU| #![auto]
        initial.contains_key(root)
        && selected.contains(root)
        && !initial[root].snapshots.frozen
        && initial[root].summary.contains(au))
}

proof fn freeze_branch_selected_insert(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
    root: AU,
)
    requires
        initial.contains_key(root),
        !selected.contains(root),
    ensures
        freeze_branch_selected(initial, selected).insert(
            root,
            BranchSummaryRecordView {
                summary: initial[root].summary,
                snapshots: initial[root].snapshots.freeze(),
            },
        ) == freeze_branch_selected(initial, selected.insert(root)),
{
    assert_maps_equal!(
        freeze_branch_selected(initial, selected).insert(
            root,
            BranchSummaryRecordView {
                summary: initial[root].summary,
                snapshots: initial[root].snapshots.freeze(),
            },
        ),
        freeze_branch_selected(initial, selected.insert(root)),
        candidate => { }
    );
}

proof fn commit_active_branch_selected_insert(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
    root: AU,
)
    requires
        initial.contains_key(root),
        !selected.contains(root),
    ensures
        commit_active_branch_selected(initial, selected).insert(
            root,
            BranchSummaryRecordView {
                summary: initial[root].summary,
                snapshots: initial[root].snapshots.commit_complete(),
            },
        ) == commit_active_branch_selected(initial, selected.insert(root)),
{
    assert_maps_equal!(
        commit_active_branch_selected(initial, selected).insert(
            root,
            BranchSummaryRecordView {
                summary: initial[root].summary,
                snapshots: initial[root].snapshots.commit_complete(),
            },
        ),
        commit_active_branch_selected(initial, selected.insert(root)),
        candidate => { }
    );
}

proof fn commit_retired_branch_selected_insert(
    initial: Map<AU, BranchSummaryRecordView>,
    selected: Set<AU>,
    root: AU,
)
    requires
        initial.contains_key(root),
        !selected.contains(root),
    ensures
        (if initial[root].snapshots.frozen {
            commit_retired_branch_selected(initial, selected).insert(
                root,
                BranchSummaryRecordView {
                    summary: initial[root].summary,
                    snapshots: initial[root].snapshots.commit_complete(),
                },
            )
        } else {
            commit_retired_branch_selected(initial, selected).remove(root)
        }) == commit_retired_branch_selected(initial, selected.insert(root)),
        retired_branch_reclaimed_set(initial, selected.insert(root))
            =~= if initial[root].snapshots.frozen {
                retired_branch_reclaimed_set(initial, selected)
            } else {
                retired_branch_reclaimed_set(initial, selected)
                    + initial[root].summary
            },
{
    assert_maps_equal!(
        if initial[root].snapshots.frozen {
            commit_retired_branch_selected(initial, selected).insert(
                root,
                BranchSummaryRecordView {
                    summary: initial[root].summary,
                    snapshots: initial[root].snapshots.commit_complete(),
                },
            )
        } else {
            commit_retired_branch_selected(initial, selected).remove(root)
        },
        commit_retired_branch_selected(initial, selected.insert(root)),
        candidate => { }
    );
    assert forall |au: AU|
        #![trigger retired_branch_reclaimed_set(
            initial,
            selected.insert(root),
        ).contains(au)]
        retired_branch_reclaimed_set(initial, selected.insert(root)).contains(au)
        == (if initial[root].snapshots.frozen {
            retired_branch_reclaimed_set(initial, selected)
        } else {
            retired_branch_reclaimed_set(initial, selected)
                + initial[root].summary
        }).contains(au) by {
        if retired_branch_reclaimed_set(
            initial,
            selected.insert(root),
        ).contains(au) {
            let owner = choose |owner: AU| #![auto]
                initial.contains_key(owner)
                && selected.insert(root).contains(owner)
                && !initial[owner].snapshots.frozen
                && initial[owner].summary.contains(au);
            if owner == root {
                assert(!initial[root].snapshots.frozen);
            } else {
                assert(selected.contains(owner));
                assert(retired_branch_reclaimed_set(initial, selected)
                    .contains(au));
            }
        } else if (if initial[root].snapshots.frozen {
            retired_branch_reclaimed_set(initial, selected)
        } else {
            retired_branch_reclaimed_set(initial, selected)
                + initial[root].summary
        }).contains(au) {
            if retired_branch_reclaimed_set(initial, selected).contains(au) {
                let owner = choose |owner: AU| #![auto]
                    initial.contains_key(owner)
                    && selected.contains(owner)
                    && !initial[owner].snapshots.frozen
                    && initial[owner].summary.contains(au);
                assert(selected.insert(root).contains(owner));
                assert(retired_branch_reclaimed_set(
                    initial,
                    selected.insert(root),
                ).contains(au));
            } else {
                assert(!initial[root].snapshots.frozen);
                assert(initial[root].summary.contains(au));
                assert(selected.insert(root).contains(root));
                assert(exists |owner: AU| #![auto]
                    initial.contains_key(owner)
                    && selected.insert(root).contains(owner)
                    && !initial[owner].snapshots.frozen
                    && initial[owner].summary.contains(au));
                assert(retired_branch_reclaimed_set(
                    initial,
                    selected.insert(root),
                ).contains(au));
            }
        }
    }

}

impl BranchSummaryOwnershipImpl {

    pub fn commit_complete(&mut self) -> (reclaimed: Vec<IAU>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            self.all_summary_aus() <= old(self).all_summary_aus(),
            self.active_summary_map() == old(self).active_summary_map(),
            self.active_summary_aus() =~= old(self).active_summary_aus(),
            self.persistent_aus() =~= old(self).frozen_aus(),
            self.frozen_aus() =~= Set::<AU>::empty(),
            unique_iau_seq(reclaimed@),
            iau_seq_set(reclaimed@)
                =~= old(self).persistent_aus()
                    - old(self).frozen_aus()
                    - old(self).active_summary_aus(),
    {
        let active_bucket_count = self.active.bucket_count;
        let retired_bucket_count = self.retired.bucket_count;
        let active_roots = self.active.roots();
        let retired_roots = self.retired.roots();
        let ghost initial_active = self.active@;
        let ghost initial_retired = self.retired@;
        let ghost initial_active_summary_aus = self.active_summary_aus();
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();

        let mut active_index = 0usize;
        while active_index < active_roots.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                unique_iau_seq(active_roots@),
                iau_seq_set(active_roots@) =~= initial_active.dom(),
                active_index <= active_roots.len(),
                self.retired@ == initial_retired,
                self.active@
                    == commit_active_branch_selected(
                        initial_active,
                        iau_seq_set(active_roots@.take(active_index as int)),
                    ),
            decreases active_roots.len() - active_index,
        {
            let root = active_roots[active_index];
            let snapshots = self.active.get_snapshots(root);
            proof {
                assert(initial_active.contains_key(root as nat));
                assert(snapshots is Some);
                assert(!iau_seq_set(active_roots@.take(active_index as int))
                    .contains(root as nat)) by {
                    if iau_seq_set(active_roots@.take(active_index as int))
                        .contains(root as nat)
                    {
                        let earlier = choose |i: int| #![auto]
                            0 <= i < active_roots@.take(active_index as int).len()
                            && active_roots@.take(active_index as int)[i] == root;
                        assert(active_roots@[earlier]
                            == active_roots@[active_index as int]);
                        assert(earlier != active_index);
                    }
                }
                assert(snapshots.unwrap() == initial_active[root as nat].snapshots);
            }
            let mut snapshots = snapshots.unwrap();
            snapshots.finish_commit();
            self.active.set_snapshots(root, snapshots);
            proof {
                let ghost selected = iau_seq_set(
                    active_roots@.take(active_index as int),
                );
                commit_active_branch_selected_insert(
                    initial_active,
                    selected,
                    root as nat,
                );
                assert(active_roots@.take(active_index as int + 1)
                    == active_roots@.take(active_index as int).push(root));
                iau_seq_set_push(active_roots@.take(active_index as int), root);
                assert(self.active@
                    == commit_active_branch_selected(
                        initial_active,
                        iau_seq_set(active_roots@.take(active_index as int + 1)),
                    ));
                assert(self.summaries_pairwise_disjoint()) by {
                    assert forall |left: AU, right: AU|
                        #![trigger self.records().contains_key(left), self.records().contains_key(right)]
                        self.records().contains_key(left)
                        && self.records().contains_key(right)
                        && left != right
                        implies self.records()[left].summary.disjoint(
                            self.records()[right].summary,
                        ) by {
                        assert(self.records()[left].summary
                            == old(self).records()[left].summary);
                        assert(self.records()[right].summary
                            == old(self).records()[right].summary);
                        assert(old(self).records().contains_key(left));
                        assert(old(self).records().contains_key(right));
                        assert(old(self).summaries_pairwise_disjoint());
                        assert(old(self).records()[left].summary.disjoint(
                            old(self).records()[right].summary,
                        ));
                    }
                }
                assert(self.wf());
            }
            active_index += 1;
        }

        let ghost committed_active = self.active@;
        let mut reclaimed = Vec::<IAU>::new();
        let mut retired_index = 0usize;
        while retired_index < retired_roots.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                unique_iau_seq(retired_roots@),
                iau_seq_set(retired_roots@) =~= initial_retired.dom(),
                retired_index <= retired_roots.len(),
                self.active@ == committed_active,
                self.retired@
                    == commit_retired_branch_selected(
                        initial_retired,
                        iau_seq_set(retired_roots@.take(retired_index as int)),
                    ),
                unique_iau_seq(reclaimed@),
                iau_seq_set(reclaimed@)
                    =~= retired_branch_reclaimed_set(
                        initial_retired,
                        iau_seq_set(retired_roots@.take(retired_index as int)),
                    ),
            decreases retired_roots.len() - retired_index,
        {
            let root = retired_roots[retired_index];
            let snapshots = self.retired.get_snapshots(root);
            let ghost selected = iau_seq_set(
                retired_roots@.take(retired_index as int),
            );
            let ghost before_reclaimed_set = iau_seq_set(reclaimed@);
            proof {
                assert(initial_retired.contains_key(root as nat));
                assert(snapshots is Some);
                assert(!selected.contains(root as nat)) by {
                    if selected.contains(root as nat) {
                        let earlier = choose |i: int| #![auto]
                            0 <= i < retired_roots@.take(retired_index as int).len()
                            && retired_roots@.take(retired_index as int)[i] == root;
                        assert(retired_roots@[earlier]
                            == retired_roots@[retired_index as int]);
                        assert(earlier != retired_index);
                    }
                }
                assert(snapshots.unwrap()
                    == initial_retired[root as nat].snapshots);
            }
            if snapshots.unwrap().frozen {
                let mut snapshots = snapshots.unwrap();
                snapshots.finish_commit();
                self.retired.set_snapshots(root, snapshots);
            } else {
                let record = self.retired.take(root);
                proof { assert(record is Some); }
                let record = record.unwrap();
                let ghost record_view = record@;
                let summary = record.summary;
                proof {
                    assert(record_view == initial_retired[root as nat]);
                    assert(unique_iau_seq(summary@));
                    assert(iau_seq_set(summary@) == record_view.summary);
                    assert(before_reclaimed_set.disjoint(iau_seq_set(summary@))) by {
                        assert forall |au: AU|
                            #![trigger before_reclaimed_set.contains(au)]
                            before_reclaimed_set.contains(au)
                            implies !iau_seq_set(summary@).contains(au) by {
                            if iau_seq_set(summary@).contains(au) {
                                let old_root = choose |old_root: AU| #![auto]
                                    initial_retired.contains_key(old_root)
                                    && selected.contains(old_root)
                                    && !initial_retired[old_root].snapshots.frozen
                                    && initial_retired[old_root].summary.contains(au);
                                assert(old_root != root as nat);
                                assert(old(self).records().contains_key(old_root));
                                assert(old(self).records().contains_key(root as nat));
                                assert(old(self).summaries_pairwise_disjoint());
                                assert(old(self).records()[old_root].summary.disjoint(
                                    old(self).records()[root as nat].summary,
                                ));
                            }
                        }
                    }
                }
                append_unique_aus(&mut reclaimed, summary);
            }
            proof {
                commit_retired_branch_selected_insert(
                    initial_retired,
                    selected,
                    root as nat,
                );
                assert(retired_roots@.take(retired_index as int + 1)
                    == retired_roots@.take(retired_index as int).push(root));
                iau_seq_set_push(retired_roots@.take(retired_index as int), root);
                assert(self.retired@
                    == commit_retired_branch_selected(
                        initial_retired,
                        iau_seq_set(retired_roots@.take(retired_index as int + 1)),
                    ));
                assert(before_reclaimed_set
                    =~= retired_branch_reclaimed_set(
                        initial_retired,
                        selected,
                    ));
                assert(iau_seq_set(reclaimed@)
                    =~= if initial_retired[root as nat].snapshots.frozen {
                        before_reclaimed_set
                    } else {
                        before_reclaimed_set
                            + initial_retired[root as nat].summary
                    });
                assert(iau_seq_set(reclaimed@)
                    =~= retired_branch_reclaimed_set(
                        initial_retired,
                        iau_seq_set(retired_roots@.take(retired_index as int + 1)),
                    ));
                assert(self.summaries_pairwise_disjoint()) by {
                    assert forall |left: AU, right: AU|
                        #![trigger self.records().contains_key(left), self.records().contains_key(right)]
                        self.records().contains_key(left)
                        && self.records().contains_key(right)
                        && left != right
                        implies self.records()[left].summary.disjoint(
                            self.records()[right].summary,
                        ) by {
                        assert(old(self).records().contains_key(left));
                        assert(old(self).records().contains_key(right));
                        assert(self.records()[left].summary
                            == old(self).records()[left].summary);
                        assert(self.records()[right].summary
                            == old(self).records()[right].summary);
                        assert(old(self).records()[left].summary.disjoint(
                            old(self).records()[right].summary,
                        ));
                    }
                }
                assert(self.wf());
            }
            retired_index += 1;
        }

        proof {
            assert(active_roots@.take(active_index as int) == active_roots@);
            assert(retired_roots@.take(retired_index as int) == retired_roots@);
            assert(iau_seq_set(active_roots@) =~= initial_active.dom());
            assert(iau_seq_set(retired_roots@) =~= initial_retired.dom());
            assert(self.all_summary_aus()
                <= old(self).all_summary_aus()) by {
                assert forall |au: AU|
                    #![trigger self.all_summary_aus().contains(au)]
                    self.all_summary_aus().contains(au)
                    implies old(self).all_summary_aus().contains(au) by {
                    let root = choose |root: AU| #![auto]
                        self.records().contains_key(root)
                        && self.records()[root].summary.contains(au);
                    assert(old(self).records().contains_key(root));
                    assert(old(self).records()[root].summary.contains(au));
                }
            }
            assert(self.active_summary_map() == old(self).active_summary_map()) by {
                assert_maps_equal!(
                    self.active_summary_map(),
                    old(self).active_summary_map(),
                    root => { }
                );
            }
            assert(self.active_summary_aus()
                =~= initial_active_summary_aus) by {
                assert forall |au: AU|
                    #![trigger self.active_summary_aus().contains(au)]
                    self.active_summary_aus().contains(au)
                    == initial_active_summary_aus.contains(au) by {
                    if self.active_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.active@.contains_key(root)
                            && self.active@[root].summary.contains(au);
                        assert(initial_active.contains_key(root));
                    } else if initial_active_summary_aus.contains(au) {
                        let root = choose |root: AU| #![auto]
                            initial_active.contains_key(root)
                            && initial_active[root].summary.contains(au);
                        assert(self.active@.contains_key(root));
                    }
                }
            }
            assert(self.persistent_aus() =~= initial_frozen) by {
                assert forall |au: AU|
                    #![trigger self.persistent_aus().contains(au)]
                    self.persistent_aus().contains(au)
                    == initial_frozen.contains(au) by {
                    if self.persistent_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].snapshots.persistent
                            && self.records()[root].summary.contains(au);
                        assert(old(self).records().contains_key(root));
                        assert(old(self).records()[root].snapshots.frozen);
                    } else if initial_frozen.contains(au) {
                        let root = choose |root: AU| #![auto]
                            old(self).records().contains_key(root)
                            && old(self).records()[root].snapshots.frozen
                            && old(self).records()[root].summary.contains(au);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].snapshots.persistent);
                    }
                }
            }
            assert(self.frozen_aus() =~= Set::<AU>::empty()) by {
                assert forall |au: AU|
                    #![trigger self.frozen_aus().contains(au)]
                    !self.frozen_aus().contains(au) by { }
            }
            assert(iau_seq_set(reclaimed@)
                =~= initial_persistent
                    - initial_frozen
                    - initial_active_summary_aus) by {
                assert forall |au: AU|
                    #![trigger iau_seq_set(reclaimed@).contains(au)]
                    iau_seq_set(reclaimed@).contains(au)
                    == (initial_persistent
                        - initial_frozen
                        - initial_active_summary_aus).contains(au) by {
                    if iau_seq_set(reclaimed@).contains(au) {
                        let root = choose |root: AU| #![auto]
                            initial_retired.contains_key(root)
                            && !initial_retired[root].snapshots.frozen
                            && initial_retired[root].summary.contains(au);
                        assert(initial_retired[root].snapshots.persistent);
                        assert((initial_active.union_prefer_right(initial_retired))
                            .contains_key(root));
                        assert((initial_active.union_prefer_right(initial_retired))[root]
                            .snapshots.persistent);
                        assert((initial_active.union_prefer_right(initial_retired))[root]
                            .summary.contains(au));
                        assert(exists |owner: AU| #![auto]
                            (initial_active.union_prefer_right(initial_retired))
                                .contains_key(owner)
                            && (initial_active.union_prefer_right(initial_retired))[owner]
                                .snapshots.persistent
                            && (initial_active.union_prefer_right(initial_retired))[owner]
                                .summary.contains(au));
                        assert(initial_persistent.contains(au));
                        assert(!initial_frozen.contains(au)) by {
                            if initial_frozen.contains(au) {
                                let frozen_root = choose |owner: AU| #![auto]
                                    (initial_active.union_prefer_right(initial_retired))
                                        .contains_key(owner)
                                    && (initial_active.union_prefer_right(initial_retired))[owner]
                                        .snapshots.frozen
                                    && (initial_active.union_prefer_right(initial_retired))[owner]
                                        .summary.contains(au);
                                assert(frozen_root != root);
                                assert(old(self).records()[root].summary.disjoint(
                                    old(self).records()[frozen_root].summary,
                                ));
                            }
                        }
                        assert(!initial_active_summary_aus.contains(au)) by {
                            if initial_active_summary_aus.contains(au) {
                                let active_root = choose |owner: AU| #![auto]
                                    initial_active.contains_key(owner)
                                    && initial_active[owner].summary.contains(au);
                                assert(active_root != root);
                                assert(old(self).records().contains_key(root));
                                assert(old(self).records().contains_key(active_root));
                                assert(old(self).summaries_pairwise_disjoint());
                                assert(old(self).records()[root].summary.disjoint(
                                    old(self).records()[active_root].summary,
                                ));
                            }
                        }
                    } else if (initial_persistent
                        - initial_frozen
                        - initial_active_summary_aus).contains(au)
                    {
                        let root = choose |root: AU| #![auto]
                            old(self).records().contains_key(root)
                            && old(self).records()[root].snapshots.persistent
                            && old(self).records()[root].summary.contains(au);
                        assert(initial_retired.contains_key(root));
                        assert(!initial_retired[root].snapshots.frozen);
                        assert(retired_branch_reclaimed_set(
                            initial_retired,
                            initial_retired.dom(),
                        ).contains(au));
                    }
                }
            }
            assert(initial_active == old(self).active@);
            assert(initial_retired == old(self).retired@);
            assert(initial_active_summary_aus
                =~= old(self).active_summary_aus());
            assert(initial_persistent =~= old(self).persistent_aus());
            assert(initial_frozen =~= old(self).frozen_aus());
        }
        proof {
            assert(self.active.bucket_count == active_bucket_count);
            assert(self.retired.bucket_count == retired_bucket_count);
        }
        reclaimed
    }
}

#[derive(Debug)]
pub enum BranchOwnershipUpdateResult {
    Applied { reclaimed: Vec<IAU> },
    Noop,
}

impl BranchSummaryRecord {
    pub open spec fn summary_set(&self) -> Summary {
        iau_seq_set(self.summary@)
    }

    pub open spec fn wf(&self) -> bool {
        &&& unique_iau_seq(self.summary@)
        &&& self.summary_set().contains(self.root_au as nat)
    }

    pub open spec fn header(&self) -> BranchSummaryHeader {
        BranchSummaryHeader {
            root_au: self.root_au,
            snapshots: self.snapshots,
        }
    }
}

impl View for BranchSummaryRecord {
    type V = BranchSummaryRecordView;

    open spec fn view(&self) -> Self::V {
        BranchSummaryRecordView {
            summary: self.summary_set(),
            snapshots: self.snapshots,
        }
    }
}

impl BranchSummaryBucket {
    pub open spec fn unique_roots(entries: Seq<BranchSummaryRecord>) -> bool {
        forall |i: int, j: int|
            #![trigger entries[i].root_au, entries[j].root_au]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i].root_au == entries[j].root_au
            ==> i == j
    }

    pub open spec fn entries_wf(entries: Seq<BranchSummaryRecord>) -> bool {
        forall |i: int| #![trigger entries[i]]
            0 <= i < entries.len() ==> entries[i].wf()
    }

    pub open spec fn entries_map(
        entries: Seq<BranchSummaryRecord>,
    ) -> Map<AU, BranchSummaryRecordView>
        recommends Self::unique_roots(entries)
    {
        Map::new(
            |root: AU| exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].root_au as nat == root,
            |root: AU| entries[choose |i: int| #![auto]
                0 <= i < entries.len()
                && entries[i].root_au as nat == root]@,
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& Self::unique_roots(self.entries@)
        &&& Self::entries_wf(self.entries@)
    }

    pub open spec fn summary_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |root: AU| #![auto]
            self@.contains_key(root)
            && self@[root].summary.contains(au))
    }

    pub open spec fn summary_aus_prefix(
        entries: Seq<BranchSummaryRecord>,
        count: nat,
    ) -> Set<AU> {
        Set::new(|au: AU| exists |entry: int| #![auto]
            0 <= entry < count
            && entry < entries.len()
            && entries[entry].summary_set().contains(au))
    }

    fn contains_summary_au(&self, au: IAU) -> (out: bool)
        requires self.wf(),
        ensures out == self.summary_aus().contains(au as nat),
    {
        let mut record_index = 0usize;
        while record_index < self.entries.len()
            invariant
                self.wf(),
                record_index <= self.entries.len(),
                forall |i: int| #![trigger self.entries@[i]]
                    0 <= i < record_index
                    ==> !self.entries@[i].summary_set().contains(au as nat),
            decreases self.entries.len() - record_index,
        {
            let mut summary_index = 0usize;
            while summary_index < self.entries[record_index].summary.len()
                invariant
                    self.wf(),
                    record_index < self.entries.len(),
                    summary_index
                        <= self.entries@[record_index as int].summary@.len(),
                    forall |i: int| #![trigger
                        self.entries@[record_index as int].summary@[i]]
                        0 <= i < summary_index
                        ==> self.entries@[record_index as int].summary@[i] != au,
                decreases self.entries@[record_index as int].summary@.len()
                    - summary_index as nat,
            {
                if self.entries[record_index].summary[summary_index] == au {
                    proof {
                        let root = self.entries@[record_index as int].root_au as nat;
                        Self::entries_map_index(
                            self.entries@,
                            record_index as int,
                        );
                        assert(self.entries@[record_index as int]
                            .summary_set().contains(au as nat));
                        assert(self.summary_aus().contains(au as nat));
                    }
                    return true;
                }
                summary_index += 1;
            }
            proof {
                assert(!self.entries@[record_index as int]
                    .summary_set().contains(au as nat)) by {
                    if self.entries@[record_index as int]
                        .summary_set().contains(au as nat)
                    {
                        let i = choose |i: int| #![auto]
                            0 <= i < self.entries@[record_index as int]
                                .summary@.len()
                            && self.entries@[record_index as int].summary@[i]
                                as nat == au as nat;
                        assert(i < summary_index);
                    }
                }
            }
            record_index += 1;
        }
        proof {
            assert(!self.summary_aus().contains(au as nat)) by {
                if self.summary_aus().contains(au as nat) {
                    let root = choose |root: AU| #![auto]
                        self@.contains_key(root)
                        && self@[root].summary.contains(au as nat);
                    let i = Self::entries_map_index_for_root(self.entries@, root);
                    assert(i < record_index);
                    assert(self.entries@[i].summary_set().contains(au as nat));
                }
            }
        }
        false
    }

    proof fn entries_map_index(entries: Seq<BranchSummaryRecord>, i: int)
        requires
            Self::unique_roots(entries),
            0 <= i < entries.len(),
        ensures
            Self::entries_map(entries).contains_key(entries[i].root_au as nat),
            Self::entries_map(entries)[entries[i].root_au as nat] == entries[i]@,
    {
    }

    proof fn entries_map_index_for_root(
        entries: Seq<BranchSummaryRecord>,
        root: AU,
    ) -> (i: int)
        requires
            Self::unique_roots(entries),
            Self::entries_map(entries).contains_key(root),
        ensures
            0 <= i < entries.len(),
            entries[i].root_au as nat == root,
            Self::entries_map(entries)[root] == entries[i]@,
    {
        let i = choose |i: int| #![auto]
            0 <= i < entries.len() && entries[i].root_au as nat == root;
        Self::entries_map_index(entries, i);
        i
    }

    proof fn entries_map_after_push(
        old_entries: Seq<BranchSummaryRecord>,
        entry: BranchSummaryRecord,
    )
        requires
            Self::unique_roots(old_entries),
            Self::entries_wf(old_entries),
            entry.wf(),
            !Self::entries_map(old_entries).contains_key(entry.root_au as nat),
        ensures
            Self::unique_roots(old_entries.push(entry)),
            Self::entries_wf(old_entries.push(entry)),
            Self::entries_map(old_entries.push(entry))
                == Self::entries_map(old_entries).insert(entry.root_au as nat, entry@),
    {
        let new_entries = old_entries.push(entry);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].root_au, new_entries[j].root_au]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].root_au == new_entries[j].root_au
            implies i == j by {
            if i < old_entries.len() && j < old_entries.len() {
                assert(new_entries[i] == old_entries[i]);
                assert(new_entries[j] == old_entries[j]);
            } else if i == old_entries.len() && j < old_entries.len() {
                assert(Self::entries_map(old_entries)
                    .contains_key(old_entries[j].root_au as nat));
            } else if i < old_entries.len() && j == old_entries.len() {
                assert(Self::entries_map(old_entries)
                    .contains_key(old_entries[i].root_au as nat));
            }
        }
        assert forall |i: int| #![trigger new_entries[i]]
            0 <= i < new_entries.len() implies new_entries[i].wf() by {
            if i < old_entries.len() {
                assert(new_entries[i] == old_entries[i]);
            } else {
                assert(i == old_entries.len());
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(entry.root_au as nat, entry@),
            root => {
                if root == entry.root_au as nat {
                    Self::entries_map_index(new_entries, old_entries.len() as int);
                } else if Self::entries_map(old_entries).contains_key(root) {
                    let i = Self::entries_map_index_for_root(old_entries, root);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    proof fn entries_map_after_remove(
        old_entries: Seq<BranchSummaryRecord>,
        index: int,
    )
        requires
            Self::unique_roots(old_entries),
            Self::entries_wf(old_entries),
            0 <= index < old_entries.len(),
        ensures
            Self::unique_roots(old_entries.remove(index)),
            Self::entries_wf(old_entries.remove(index)),
            Self::entries_map(old_entries.remove(index))
                == Self::entries_map(old_entries)
                    .remove(old_entries[index].root_au as nat),
    {
        let new_entries = old_entries.remove(index);
        assert forall |i: int, j: int|
            #![trigger new_entries[i].root_au, new_entries[j].root_au]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].root_au == new_entries[j].root_au
            implies i == j by {
            let old_i = if i < index { i } else { i + 1 };
            let old_j = if j < index { j } else { j + 1 };
            assert(new_entries[i] == old_entries[old_i]);
            assert(new_entries[j] == old_entries[old_j]);
            assert(old_i == old_j);
        }
        assert forall |i: int| #![trigger new_entries[i]]
            0 <= i < new_entries.len() implies new_entries[i].wf() by {
            let old_i = if i < index { i } else { i + 1 };
            assert(new_entries[i] == old_entries[old_i]);
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries)
                .remove(old_entries[index].root_au as nat),
            root => {
                if Self::entries_map(new_entries).contains_key(root) {
                    let i = Self::entries_map_index_for_root(new_entries, root);
                    let old_i = if i < index { i } else { i + 1 };
                    assert(new_entries[i] == old_entries[old_i]);
                    Self::entries_map_index(old_entries, old_i);
                }
                if Self::entries_map(old_entries).contains_key(root)
                    && root != old_entries[index].root_au as nat
                {
                    let old_i = Self::entries_map_index_for_root(old_entries, root);
                    assert(old_i != index);
                    let i = if old_i < index { old_i } else { old_i - 1 };
                    assert(new_entries[i] == old_entries[old_i]);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    proof fn entries_map_after_snapshot_set(
        old_entries: Seq<BranchSummaryRecord>,
        index: int,
        snapshots: SnapshotMembership,
    )
        requires
            Self::unique_roots(old_entries),
            Self::entries_wf(old_entries),
            0 <= index < old_entries.len(),
        ensures
            Self::unique_roots(old_entries.update(
                index,
                BranchSummaryRecord {
                    root_au: old_entries[index].root_au,
                    summary: old_entries[index].summary,
                    snapshots,
                },
            )),
            Self::entries_wf(old_entries.update(
                index,
                BranchSummaryRecord {
                    root_au: old_entries[index].root_au,
                    summary: old_entries[index].summary,
                    snapshots,
                },
            )),
            Self::entries_map(old_entries.update(
                index,
                BranchSummaryRecord {
                    root_au: old_entries[index].root_au,
                    summary: old_entries[index].summary,
                    snapshots,
                },
            )) == Self::entries_map(old_entries).insert(
                old_entries[index].root_au as nat,
                BranchSummaryRecordView {
                    summary: old_entries[index].summary_set(),
                    snapshots,
                },
            ),
    {
        let old = old_entries[index];
        let entry = BranchSummaryRecord {
            root_au: old.root_au,
            summary: old.summary,
            snapshots,
        };
        let new_entries = old_entries.update(index, entry);
        assert(entry.wf());
        assert forall |i: int, j: int|
            #![trigger new_entries[i].root_au, new_entries[j].root_au]
            0 <= i < new_entries.len()
            && 0 <= j < new_entries.len()
            && new_entries[i].root_au == new_entries[j].root_au
            implies i == j by {
            if i != index && j != index {
                assert(new_entries[i] == old_entries[i]);
                assert(new_entries[j] == old_entries[j]);
            } else if i == index && j != index {
                assert(old_entries[index].root_au == old_entries[j].root_au);
            } else if i != index && j == index {
                assert(old_entries[i].root_au == old_entries[index].root_au);
            }
        }
        assert forall |i: int| #![trigger new_entries[i]]
            0 <= i < new_entries.len() implies new_entries[i].wf() by {
            if i != index {
                assert(new_entries[i] == old_entries[i]);
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(
                old.root_au as nat,
                BranchSummaryRecordView {
                    summary: old.summary_set(),
                    snapshots,
                },
            ),
            root => {
                if root == old.root_au as nat {
                    Self::entries_map_index(new_entries, index);
                } else if Self::entries_map(old_entries).contains_key(root) {
                    let i = Self::entries_map_index_for_root(old_entries, root);
                    assert(i != index);
                    Self::entries_map_index(new_entries, i);
                }
            }
        );
    }

    fn new() -> (out: Self)
        ensures
            out.wf(),
            out@ == Map::<AU, BranchSummaryRecordView>::empty(),
            out.entries@.len() == 0,
    {
        let out = Self { entries: Vec::new() };
        assert(out@ == Map::<AU, BranchSummaryRecordView>::empty());
        out
    }

    fn get_snapshots(&self, root_au: IAU) -> (out: Option<SnapshotMembership>)
        requires self.wf(),
        ensures
            (out is Some) == self@.contains_key(root_au as nat),
            out is Some ==> out.unwrap() == self@[root_au as nat].snapshots,
    {
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].root_au != root_au,
            decreases self.entries.len() - index,
        {
            if self.entries[index].root_au == root_au {
                proof { Self::entries_map_index(self.entries@, index as int); }
                return Some(self.entries[index].snapshots);
            }
            index += 1;
        }
        proof {
            assert(!self@.contains_key(root_au as nat)) by {
                if self@.contains_key(root_au as nat) {
                    let i = Self::entries_map_index_for_root(
                        self.entries@,
                        root_au as nat,
                    );
                    assert(i < index);
                    assert(self.entries@[i].root_au == root_au);
                }
            }
        }
        None
    }

    fn insert(&mut self, record: BranchSummaryRecord)
        requires
            old(self).wf(),
            record.wf(),
            !old(self)@.contains_key(record.root_au as nat),
        ensures
            self.wf(),
            self@ == old(self)@.insert(record.root_au as nat, record@),
            forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                ==> self.entries@[i].root_au == record.root_au
                    || exists |old_i: int| #![auto]
                        0 <= old_i < old(self).entries@.len()
                        && old(self).entries@[old_i].root_au
                            == self.entries@[i].root_au,
    {
        let ghost old_entries = self.entries@;
        self.entries.push(record);
        proof {
            Self::entries_map_after_push(old_entries, record);
            assert forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                implies self.entries@[i].root_au == record.root_au
                    || exists |old_i: int| #![auto]
                        0 <= old_i < old_entries.len()
                        && old_entries[old_i].root_au
                            == self.entries@[i].root_au by {
                if i < old_entries.len() {
                    assert(self.entries@[i] == old_entries[i]);
                } else {
                    assert(i == old_entries.len());
                }
            }
        }
    }

    fn take(&mut self, root_au: IAU) -> (out: Option<BranchSummaryRecord>)
        requires old(self).wf(),
        ensures
            self.wf(),
            (out is Some) == old(self)@.contains_key(root_au as nat),
            out is Some ==> out.unwrap().root_au == root_au,
            out is Some ==> out.unwrap().wf(),
            out is Some ==> out.unwrap()@ == old(self)@[root_au as nat],
            self@ == old(self)@.remove(root_au as nat),
    {
        let ghost old_entries = self.entries@;
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                self.entries@ == old_entries,
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].root_au != root_au,
            decreases self.entries.len() - index,
        {
            if self.entries[index].root_au == root_au {
                let record = self.entries.remove(index);
                proof {
                    assert(record == old_entries[index as int]);
                    Self::entries_map_after_remove(old_entries, index as int);
                }
                return Some(record);
            }
            index += 1;
        }
        proof {
            assert(old_entries == old(self).entries@);
            assert(self.entries@ == old_entries);
            assert(!self@.contains_key(root_au as nat)) by {
                if self@.contains_key(root_au as nat) {
                    let i = Self::entries_map_index_for_root(old_entries, root_au as nat);
                    assert(i < index);
                }
            }
            assert(self@ == old(self)@.remove(root_au as nat));
        }
        None
    }

    fn set_snapshots(&mut self, root_au: IAU, snapshots: SnapshotMembership)
        requires
            old(self).wf(),
            old(self)@.contains_key(root_au as nat),
        ensures
            self.wf(),
            self@ == old(self)@.insert(
                root_au as nat,
                BranchSummaryRecordView {
                    summary: old(self)@[root_au as nat].summary,
                    snapshots,
                },
            ),
            self.entries@.len() == old(self).entries@.len(),
            forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                ==> self.entries@[i].root_au == old(self).entries@[i].root_au,
    {
        let ghost old_entries = self.entries@;
        let mut index = 0usize;
        while index < self.entries.len()
            invariant
                self.wf(),
                self.entries@ == old_entries,
                index <= self.entries.len(),
                forall |i: int| #![auto]
                    0 <= i < index ==> self.entries@[i].root_au != root_au,
            decreases self.entries.len() - index,
        {
            if self.entries[index].root_au == root_au {
                let old = self.entries.remove(index);
                let entry = BranchSummaryRecord {
                    root_au: old.root_au,
                    summary: old.summary,
                    snapshots,
                };
                self.entries.insert(index, entry);
                proof {
                    assert(self.entries@ == old_entries.update(index as int, entry));
                    Self::entries_map_after_snapshot_set(
                        old_entries,
                        index as int,
                        snapshots,
                    );
                    assert forall |i: int| #![trigger self.entries@[i]]
                        0 <= i < self.entries@.len()
                        implies self.entries@[i].root_au
                            == old_entries[i].root_au by {
                        if i != index {
                            assert(self.entries@[i] == old_entries[i]);
                        }
                    }
                }
                return;
            }
            index += 1;
        }
        proof {
            let i = Self::entries_map_index_for_root(old_entries, root_au as nat);
            assert(i < index);
            assert(false);
        }
    }
}

impl View for BranchSummaryBucket {
    type V = Map<AU, BranchSummaryRecordView>;

    open spec fn view(&self) -> Self::V {
        Self::entries_map(self.entries@)
    }
}

impl BranchSummaryTable {
    pub open spec fn bucket_index(root: AU, bucket_count: nat) -> nat
        recommends bucket_count > 0
    {
        root % bucket_count
    }

    pub open spec fn buckets_map(
        buckets: Seq<BranchSummaryBucket>,
        bucket_count: nat,
    ) -> Map<AU, BranchSummaryRecordView>
        recommends
            bucket_count > 0,
            buckets.len() == bucket_count,
            forall |i: int| #![trigger buckets[i]]
                0 <= i < buckets.len() ==> buckets[i].wf(),
    {
        Map::new(
            |root: AU| buckets[Self::bucket_index(root, bucket_count) as int]@
                .contains_key(root),
            |root: AU| buckets[Self::bucket_index(root, bucket_count) as int]@[root],
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.bucket_count > 0
        &&& self.buckets@.len() == self.bucket_count as nat
        &&& forall |bucket: int| #![trigger self.buckets@[bucket]]
            0 <= bucket < self.buckets@.len()
            ==> self.buckets@[bucket].wf()
        &&& forall |bucket: int, entry: int|
            #![trigger self.buckets@[bucket].entries@[entry]]
            0 <= bucket < self.buckets@.len()
            && 0 <= entry < self.buckets@[bucket].entries@.len()
            ==> Self::bucket_index(
                self.buckets@[bucket].entries@[entry].root_au as nat,
                self.bucket_count as nat,
            ) == bucket
    }

    proof fn view_domain_finite(&self)
        requires self.wf(),
        ensures self@.dom().finite(),
    {
        let int_range = set_int_range(0, u32::MAX as int + 1);
        let executable = Set::<AU>::new(|au: AU| au <= u32::MAX as nat);
        let mapped = int_range.map(|i: int| i as nat);
        lemma_int_range(0, u32::MAX as int + 1);
        int_range.lemma_map_finite(|i: int| i as nat);
        assert(executable =~= mapped) by {
            assert forall |au: AU| #[trigger] executable.contains(au)
                implies mapped.contains(au) by {
                assert(int_range.contains(au as int));
            }
            assert forall |au: AU| #[trigger] mapped.contains(au)
                implies executable.contains(au) by {
                let i = choose |i: int|
                    int_range.contains(i) && i as nat == au;
                assert(0 <= i < u32::MAX as int + 1);
            }
        }
        assert(self@.dom() <= executable) by {
            assert forall |root: AU| #[trigger] self@.dom().contains(root)
                implies executable.contains(root) by {
                let bucket = Self::bucket_index(
                    root,
                    self.bucket_count as nat,
                ) as int;
                assert(self.buckets@[bucket]@.contains_key(root));
                let index = BranchSummaryBucket::entries_map_index_for_root(
                    self.buckets@[bucket].entries@,
                    root,
                );
                assert(self.buckets@[bucket].entries@[index].root_au as nat
                    == root);
            }
        }
        lemma_set_subset_finite(executable, self@.dom());
    }

    pub open spec fn summary_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |root: AU| #![auto]
            self@.contains_key(root)
            && self@[root].summary.contains(au))
    }

    pub open spec fn summaries_pairwise_disjoint(&self) -> bool {
        forall |left: AU, right: AU|
            #![trigger self@.contains_key(left), self@.contains_key(right)]
            self@.contains_key(left)
            && self@.contains_key(right)
            && left != right
            ==> self@[left].summary.disjoint(self@[right].summary)
    }

    pub open spec fn summary_aus_prefix(
        buckets: Seq<BranchSummaryBucket>,
        count: nat,
    ) -> Set<AU> {
        Set::new(|au: AU| exists |bucket: int| #![auto]
            0 <= bucket < count
            && bucket < buckets.len()
            && buckets[bucket].summary_aus().contains(au))
    }

    pub fn flatten_summary_aus(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
            self.summaries_pairwise_disjoint(),
        ensures
            unique_iau_seq(out@),
            iau_seq_set(out@) =~= self.summary_aus(),
    {
        let mut out = Vec::<IAU>::new();
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                self.summaries_pairwise_disjoint(),
                bucket <= self.buckets.len(),
                unique_iau_seq(out@),
                iau_seq_set(out@)
                    =~= Self::summary_aus_prefix(self.buckets@, bucket as nat),
            decreases self.buckets.len() - bucket,
        {
            let mut entry = 0usize;
            let bucket_len = self.buckets[bucket].entries.len();
            while entry < bucket_len
                invariant
                    self.wf(),
                    self.summaries_pairwise_disjoint(),
                    bucket < self.buckets.len(),
                    bucket_len
                        == self.buckets@[bucket as int].entries@.len(),
                    entry <= bucket_len,
                    unique_iau_seq(out@),
                    iau_seq_set(out@)
                        =~= Self::summary_aus_prefix(
                                self.buckets@,
                                bucket as nat,
                            )
                            + BranchSummaryBucket::summary_aus_prefix(
                                self.buckets@[bucket as int].entries@,
                                entry as nat,
                            ),
                decreases bucket_len - entry,
            {
                let record = &self.buckets[bucket].entries[entry];
                let summary = copy_iau_vec(&record.summary);
                let ghost root = record.root_au as nat;
                proof {
                    assert(unique_iau_seq(summary@));
                    assert(iau_seq_set(out@).disjoint(iau_seq_set(summary@))) by {
                        assert forall |au: AU|
                            #![trigger iau_seq_set(out@).contains(au)]
                            iau_seq_set(out@).contains(au)
                            implies !iau_seq_set(summary@).contains(au) by {
                            if iau_seq_set(summary@).contains(au) {
                                if Self::summary_aus_prefix(
                                    self.buckets@,
                                    bucket as nat,
                                ).contains(au) {
                                    let old_bucket = choose |old_bucket: int| #![auto]
                                        0 <= old_bucket < bucket
                                        && self.buckets@[old_bucket]
                                            .summary_aus().contains(au);
                                    let old_root = choose |old_root: AU| #![auto]
                                        self.buckets@[old_bucket]@
                                            .contains_key(old_root)
                                        && self.buckets@[old_bucket]@[old_root]
                                            .summary.contains(au);
                                    assert(self@.contains_key(old_root));
                                    assert(self@.contains_key(root));
                                    assert(old_root != root) by {
                                        assert(Self::bucket_index(
                                            old_root,
                                            self.bucket_count as nat,
                                        ) == old_bucket);
                                        assert(Self::bucket_index(
                                            root,
                                            self.bucket_count as nat,
                                        ) == bucket);
                                    }
                                    assert(self@[old_root].summary.disjoint(
                                        self@[root].summary,
                                    ));
                                } else {
                                    let old_entry = choose |old_entry: int| #![auto]
                                        0 <= old_entry < entry
                                        && self.buckets@[bucket as int]
                                            .entries@[old_entry]
                                            .summary_set().contains(au);
                                    let old_root = self.buckets@[bucket as int]
                                        .entries@[old_entry].root_au as nat;
                                    assert(self@.contains_key(old_root));
                                    assert(self@.contains_key(root));
                                    assert(old_root != root) by {
                                        assert(self.buckets@[bucket as int].wf());
                                        assert(old_entry != entry);
                                    }
                                    assert(self@[old_root].summary.disjoint(
                                        self@[root].summary,
                                    ));
                                }
                            }
                        }
                    }
                }
                append_unique_aus(&mut out, summary);
                proof {
                    assert(BranchSummaryBucket::summary_aus_prefix(
                        self.buckets@[bucket as int].entries@,
                        entry as nat + 1,
                    ) =~= BranchSummaryBucket::summary_aus_prefix(
                        self.buckets@[bucket as int].entries@,
                        entry as nat,
                    ) + record.summary_set()) by {
                        assert forall |au: AU|
                            #![trigger BranchSummaryBucket::summary_aus_prefix(
                                self.buckets@[bucket as int].entries@,
                                entry as nat + 1,
                            ).contains(au)]
                            BranchSummaryBucket::summary_aus_prefix(
                                self.buckets@[bucket as int].entries@,
                                entry as nat + 1,
                            ).contains(au)
                            == (BranchSummaryBucket::summary_aus_prefix(
                                self.buckets@[bucket as int].entries@,
                                entry as nat,
                            ) + record.summary_set()).contains(au) by { }
                    }
                }
                entry += 1;
            }
            proof {
                assert(BranchSummaryBucket::summary_aus_prefix(
                    self.buckets@[bucket as int].entries@,
                    entry as nat,
                ) =~= self.buckets@[bucket as int].summary_aus()) by {
                    assert forall |au: AU|
                        #![trigger BranchSummaryBucket::summary_aus_prefix(
                            self.buckets@[bucket as int].entries@,
                            entry as nat,
                        ).contains(au)]
                        BranchSummaryBucket::summary_aus_prefix(
                            self.buckets@[bucket as int].entries@,
                            entry as nat,
                        ).contains(au)
                        == self.buckets@[bucket as int].summary_aus()
                            .contains(au) by {
                        if BranchSummaryBucket::summary_aus_prefix(
                            self.buckets@[bucket as int].entries@,
                            entry as nat,
                        ).contains(au)
                        {
                            let selected = choose |selected: int| #![auto]
                                0 <= selected < entry
                                && self.buckets@[bucket as int]
                                    .entries@[selected]
                                    .summary_set().contains(au);
                            let root = self.buckets@[bucket as int]
                                .entries@[selected].root_au as nat;
                            BranchSummaryBucket::entries_map_index(
                                self.buckets@[bucket as int].entries@,
                                selected,
                            );
                            assert(self.buckets@[bucket as int]@
                                .contains_key(root));
                            assert(self.buckets@[bucket as int]@[root]
                                .summary.contains(au));
                        } else if self.buckets@[bucket as int].summary_aus()
                            .contains(au)
                        {
                            let root = choose |root: AU| #![auto]
                                self.buckets@[bucket as int]@
                                    .contains_key(root)
                                && self.buckets@[bucket as int]@[root]
                                    .summary.contains(au);
                            let selected = BranchSummaryBucket::entries_map_index_for_root(
                                self.buckets@[bucket as int].entries@,
                                root,
                            );
                            assert(self.buckets@[bucket as int]
                                .entries@[selected].summary_set().contains(au));
                        }
                    }
                }
                assert(Self::summary_aus_prefix(
                    self.buckets@,
                    bucket as nat + 1,
                ) =~= Self::summary_aus_prefix(
                    self.buckets@,
                    bucket as nat,
                ) + self.buckets@[bucket as int].summary_aus()) by {
                    assert forall |au: AU|
                        #![trigger Self::summary_aus_prefix(
                            self.buckets@,
                            bucket as nat + 1,
                        ).contains(au)]
                        Self::summary_aus_prefix(
                            self.buckets@,
                            bucket as nat + 1,
                        ).contains(au)
                        == (Self::summary_aus_prefix(
                            self.buckets@,
                            bucket as nat,
                        ) + self.buckets@[bucket as int].summary_aus())
                            .contains(au) by { }
                }
            }
            bucket += 1;
        }
        proof {
            assert(Self::summary_aus_prefix(
                self.buckets@,
                bucket as nat,
            ) =~= self.summary_aus()) by {
                assert forall |au: AU|
                    #![trigger Self::summary_aus_prefix(
                        self.buckets@,
                        bucket as nat,
                    ).contains(au)]
                    Self::summary_aus_prefix(
                        self.buckets@,
                        bucket as nat,
                    ).contains(au)
                    == self.summary_aus().contains(au) by {
                    if Self::summary_aus_prefix(
                        self.buckets@,
                        bucket as nat,
                    ).contains(au)
                    {
                        let selected = choose |selected: int| #![auto]
                            0 <= selected < bucket
                            && self.buckets@[selected]
                                .summary_aus().contains(au);
                        let root = choose |root: AU| #![auto]
                            self.buckets@[selected]@.contains_key(root)
                            && self.buckets@[selected]@[root]
                                .summary.contains(au);
                        assert(Self::bucket_index(
                            root,
                            self.bucket_count as nat,
                        ) == selected);
                        assert(self@.contains_key(root));
                        assert(self@[root].summary.contains(au));
                    } else if self.summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self@.contains_key(root)
                            && self@[root].summary.contains(au);
                        let selected = Self::bucket_index(
                            root,
                            self.bucket_count as nat,
                        ) as int;
                        assert(self.buckets@[selected]
                            .summary_aus().contains(au));
                    }
                }
            }
        }
        out
    }

    pub fn contains_summary_au(&self, au: IAU) -> (out: bool)
        requires self.wf(),
        ensures out == self.summary_aus().contains(au as nat),
    {
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                bucket <= self.buckets.len(),
                forall |i: int| #![trigger self.buckets@[i]]
                    0 <= i < bucket
                    ==> !self.buckets@[i].summary_aus().contains(au as nat),
            decreases self.buckets.len() - bucket,
        {
            if self.buckets[bucket].contains_summary_au(au) {
                proof {
                    let root = choose |root: AU| #![auto]
                        self.buckets@[bucket as int]@.contains_key(root)
                        && self.buckets@[bucket as int]@[root]
                            .summary.contains(au as nat);
                    let entry = BranchSummaryBucket::entries_map_index_for_root(
                        self.buckets@[bucket as int].entries@,
                        root,
                    );
                    assert(Self::bucket_index(root, self.bucket_count as nat)
                        == bucket as nat);
                    assert(self@.contains_key(root));
                    assert(self@[root].summary.contains(au as nat));
                    assert(self.summary_aus().contains(au as nat));
                }
                return true;
            }
            bucket += 1;
        }
        proof {
            assert(!self.summary_aus().contains(au as nat)) by {
                if self.summary_aus().contains(au as nat) {
                    let root = choose |root: AU| #![auto]
                        self@.contains_key(root)
                        && self@[root].summary.contains(au as nat);
                    let selected = Self::bucket_index(
                        root,
                        self.bucket_count as nat,
                    ) as int;
                    assert(0 <= selected < bucket);
                    assert(self.buckets@[selected]@.contains_key(root));
                    assert(self.buckets@[selected]@[root]
                        .summary.contains(au as nat));
                    assert(self.buckets@[selected].summary_aus()
                        .contains(au as nat));
                }
            }
        }
        false
    }

    pub open spec fn roots_prefix_set(
        buckets: Seq<BranchSummaryBucket>,
        count: nat,
    ) -> Set<AU> {
        Set::new(|root: AU| exists |bucket: int| #![auto]
            0 <= bucket < count
            && bucket < buckets.len()
            && buckets[bucket]@.contains_key(root))
    }

    fn exec_bucket_index(root_au: IAU, bucket_count: u32) -> (out: usize)
        requires bucket_count > 0,
        ensures
            out as nat == Self::bucket_index(root_au as nat, bucket_count as nat),
            out < bucket_count as usize,
    {
        (root_au % bucket_count) as usize
    }

    fn empty_buckets(bucket_count: u32) -> (out: Vec<BranchSummaryBucket>)
        requires bucket_count > 0,
        ensures
            out@.len() == bucket_count as nat,
            forall |i: int| #![trigger out@[i]]
                0 <= i < out@.len()
                ==> out@[i].wf()
                    && out@[i]@ == Map::<AU, BranchSummaryRecordView>::empty()
                    && out@[i].entries@.len() == 0,
    {
        let mut out = Vec::<BranchSummaryBucket>::new();
        let mut index = 0usize;
        while index < bucket_count as usize
            invariant
                index <= bucket_count as usize,
                out@.len() == index,
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len()
                    ==> out@[i].wf()
                        && out@[i]@ == Map::<AU, BranchSummaryRecordView>::empty()
                        && out@[i].entries@.len() == 0,
            decreases bucket_count as usize - index,
        {
            out.push(BranchSummaryBucket::new());
            index += 1;
        }
        out
    }

    pub fn new(bucket_count: u32) -> (out: Self)
        requires bucket_count > 0,
        ensures
            out.wf(),
            out@ == Map::<AU, BranchSummaryRecordView>::empty(),
            out.bucket_count == bucket_count,
    {
        let buckets = Self::empty_buckets(bucket_count);
        let out = Self { buckets, bucket_count };
        proof {
            assert forall |bucket: int, entry: int|
                #![trigger out.buckets@[bucket].entries@[entry]]
                0 <= bucket < out.buckets@.len()
                && 0 <= entry < out.buckets@[bucket].entries@.len()
                implies Self::bucket_index(
                    out.buckets@[bucket].entries@[entry].root_au as nat,
                    out.bucket_count as nat,
                ) == bucket by {
                assert(out.buckets@[bucket].entries@.len() == 0);
            }
            assert(out.wf());
            assert_maps_equal!(
                out@,
                Map::<AU, BranchSummaryRecordView>::empty(),
                root => { }
            );
        }
        out
    }

    pub fn get_snapshots(
        &self,
        root_au: IAU,
    ) -> (out: Option<SnapshotMembership>)
        requires self.wf(),
        ensures
            (out is Some) == self@.contains_key(root_au as nat),
            out is Some ==> out.unwrap() == self@[root_au as nat].snapshots,
    {
        let bucket = Self::exec_bucket_index(root_au, self.bucket_count);
        self.buckets[bucket].get_snapshots(root_au)
    }

    pub fn insert(&mut self, record: BranchSummaryRecord)
        requires
            old(self).wf(),
            record.wf(),
            !old(self)@.contains_key(record.root_au as nat),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            self@ == old(self)@.insert(record.root_au as nat, record@),
    {
        let root_au = record.root_au;
        let bucket = Self::exec_bucket_index(root_au, self.bucket_count);
        let ghost old_buckets = self.buckets@;
        let ghost record_view = record@;
        let mut selected = self.buckets.remove(bucket);
        selected.insert(record);
        self.buckets.insert(bucket, selected);
        proof {
            assert forall |i: int| #![trigger self.buckets@[i]]
                0 <= i < self.buckets@.len()
                implies self.buckets@[i].wf() by {
                if i != bucket {
                    assert(self.buckets@[i] == old_buckets[i]);
                }
            }
            assert forall |b: int, e: int|
                #![trigger self.buckets@[b].entries@[e]]
                0 <= b < self.buckets@.len()
                && 0 <= e < self.buckets@[b].entries@.len()
                implies Self::bucket_index(
                    self.buckets@[b].entries@[e].root_au as nat,
                    self.bucket_count as nat,
                ) == b by {
                if b == bucket {
                    if self.buckets@[b].entries@[e].root_au == root_au {
                    } else {
                        assert(exists |old_e: int| #![auto]
                            0 <= old_e < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_e].root_au
                                == self.buckets@[b].entries@[e].root_au);
                        let old_e = choose |old_e: int| #![auto]
                            0 <= old_e < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_e].root_au
                                == self.buckets@[b].entries@[e].root_au;
                        assert(Self::bucket_index(
                            old_buckets[b].entries@[old_e].root_au as nat,
                            self.bucket_count as nat,
                        ) == b);
                    }
                } else {
                    assert(self.buckets@[b] == old_buckets[b]);
                }
            }
            assert(self.wf());
            assert_maps_equal!(
                self@,
                old(self)@.insert(root_au as nat, record_view),
                other_root => {
                    let other_bucket = Self::bucket_index(
                        other_root,
                        self.bucket_count as nat,
                    ) as int;
                    if other_root == root_au as nat {
                        assert(other_bucket == bucket);
                    } else if other_bucket != bucket {
                        assert(self.buckets@[other_bucket] == old_buckets[other_bucket]);
                    }
                }
            );
        }
    }

    pub fn take(
        &mut self,
        root_au: IAU,
    ) -> (out: Option<BranchSummaryRecord>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            (out is Some) == old(self)@.contains_key(root_au as nat),
            out is Some ==> out.unwrap().root_au == root_au,
            out is Some ==> out.unwrap().wf(),
            out is Some ==> out.unwrap()@ == old(self)@[root_au as nat],
            self@ == old(self)@.remove(root_au as nat),
    {
        let bucket = Self::exec_bucket_index(root_au, self.bucket_count);
        let ghost old_buckets = self.buckets@;
        let mut selected = self.buckets.remove(bucket);
        let out = selected.take(root_au);
        self.buckets.insert(bucket, selected);
        proof {
            assert forall |i: int| #![trigger self.buckets@[i]]
                0 <= i < self.buckets@.len()
                implies self.buckets@[i].wf() by {
                if i != bucket {
                    assert(self.buckets@[i] == old_buckets[i]);
                }
            }
            assert forall |b: int, e: int|
                #![trigger self.buckets@[b].entries@[e]]
                0 <= b < self.buckets@.len()
                && 0 <= e < self.buckets@[b].entries@.len()
                implies Self::bucket_index(
                    self.buckets@[b].entries@[e].root_au as nat,
                    self.bucket_count as nat,
                ) == b by {
                if b == bucket {
                    let new_root = self.buckets@[b].entries@[e].root_au as nat;
                    BranchSummaryBucket::entries_map_index(
                        self.buckets@[b].entries@,
                        e,
                    );
                    assert(self.buckets@[b]@.contains_key(new_root));
                    assert(old_buckets[b]@.contains_key(new_root));
                    let old_e = BranchSummaryBucket::entries_map_index_for_root(
                        old_buckets[b].entries@,
                        new_root,
                    );
                    assert(Self::bucket_index(
                        old_buckets[b].entries@[old_e].root_au as nat,
                        self.bucket_count as nat,
                    ) == b);
                } else {
                    assert(self.buckets@[b] == old_buckets[b]);
                }
            }
            assert(self.wf());
            assert_maps_equal!(
                self@,
                old(self)@.remove(root_au as nat),
                other_root => {
                    let other_bucket = Self::bucket_index(
                        other_root,
                        self.bucket_count as nat,
                    ) as int;
                    if other_root == root_au as nat {
                        assert(other_bucket == bucket);
                    } else if other_bucket != bucket {
                        assert(self.buckets@[other_bucket] == old_buckets[other_bucket]);
                    }
                }
            );
        }
        out
    }

    pub fn set_snapshots(
        &mut self,
        root_au: IAU,
        snapshots: SnapshotMembership,
    )
        requires
            old(self).wf(),
            old(self)@.contains_key(root_au as nat),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            self@ == old(self)@.insert(
                root_au as nat,
                BranchSummaryRecordView {
                    summary: old(self)@[root_au as nat].summary,
                    snapshots,
                },
            ),
    {
        let bucket = Self::exec_bucket_index(root_au, self.bucket_count);
        let ghost old_buckets = self.buckets@;
        let mut selected = self.buckets.remove(bucket);
        selected.set_snapshots(root_au, snapshots);
        self.buckets.insert(bucket, selected);
        proof {
            assert forall |i: int| #![trigger self.buckets@[i]]
                0 <= i < self.buckets@.len()
                implies self.buckets@[i].wf() by {
                if i != bucket {
                    assert(self.buckets@[i] == old_buckets[i]);
                }
            }
            assert forall |b: int, e: int|
                #![trigger self.buckets@[b].entries@[e]]
                0 <= b < self.buckets@.len()
                && 0 <= e < self.buckets@[b].entries@.len()
                implies Self::bucket_index(
                    self.buckets@[b].entries@[e].root_au as nat,
                    self.bucket_count as nat,
                ) == b by {
                if b == bucket {
                    assert(self.buckets@[b].entries@[e].root_au
                        == old_buckets[b].entries@[e].root_au);
                } else {
                    assert(self.buckets@[b] == old_buckets[b]);
                }
            }
            assert(self.wf());
            assert_maps_equal!(
                self@,
                old(self)@.insert(
                    root_au as nat,
                    BranchSummaryRecordView {
                        summary: old(self)@[root_au as nat].summary,
                        snapshots,
                    },
                ),
                other_root => {
                    let other_bucket = Self::bucket_index(
                        other_root,
                        self.bucket_count as nat,
                    ) as int;
                    if other_root == root_au as nat {
                        assert(other_bucket == bucket);
                    } else if other_bucket != bucket {
                        assert(self.buckets@[other_bucket] == old_buckets[other_bucket]);
                    }
                }
            );
        }
    }

    pub fn roots(&self) -> (out: Vec<IAU>)
        requires self.wf(),
        ensures
            unique_iau_seq(out@),
            iau_seq_set(out@) =~= self@.dom(),
    {
        let mut out = Vec::<IAU>::new();
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                bucket <= self.buckets.len(),
                unique_iau_seq(out@),
                iau_seq_set(out@)
                    =~= Self::roots_prefix_set(self.buckets@, bucket as nat),
            decreases self.buckets.len() - bucket,
        {
            let mut entry = 0usize;
            let bucket_len = self.buckets[bucket].entries.len();
            while entry < bucket_len
                invariant
                    self.wf(),
                    bucket < self.buckets.len(),
                    bucket_len == self.buckets@[bucket as int].entries@.len(),
                    entry <= self.buckets@[bucket as int].entries@.len(),
                    unique_iau_seq(out@),
                    iau_seq_set(out@)
                        =~= Self::roots_prefix_set(self.buckets@, bucket as nat)
                            + BranchSummaryBucket::entries_map(
                                self.buckets@[bucket as int].entries@
                                    .take(entry as int),
                            ).dom(),
                decreases bucket_len - entry,
            {
                let root = self.buckets[bucket].entries[entry].root_au;
                let ghost before = out@;
                proof {
                    BranchSummaryBucket::entries_map_index(
                        self.buckets@[bucket as int].entries@,
                        entry as int,
                    );
                    assert(!iau_seq_set(out@).contains(root as nat)) by {
                        if Self::roots_prefix_set(
                            self.buckets@,
                            bucket as nat,
                        ).contains(root as nat) {
                            let old_bucket = choose |old_bucket: int| #![auto]
                                0 <= old_bucket < bucket
                                && old_bucket < self.buckets@.len()
                                && self.buckets@[old_bucket]@
                                    .contains_key(root as nat);
                            let old_entry = BranchSummaryBucket::entries_map_index_for_root(
                                self.buckets@[old_bucket].entries@,
                                root as nat,
                            );
                            assert(Self::bucket_index(
                                root as nat,
                                self.bucket_count as nat,
                            ) == old_bucket);
                            assert(Self::bucket_index(
                                root as nat,
                                self.bucket_count as nat,
                            ) == bucket);
                        } else if BranchSummaryBucket::entries_map(
                            self.buckets@[bucket as int].entries@
                                .take(entry as int),
                        ).contains_key(root as nat) {
                            let old_entry = BranchSummaryBucket::entries_map_index_for_root(
                                self.buckets@[bucket as int].entries@
                                    .take(entry as int),
                                root as nat,
                            );
                            assert(self.buckets@[bucket as int].entries@[old_entry]
                                .root_au == root);
                            assert(old_entry != entry);
                        }
                    }
                }
                out.push(root);
                proof {
                    assert(out@ == before.push(root));
                    iau_seq_set_push(before, root);
                    assert(unique_iau_seq(out@));
                    assert(self.buckets@[bucket as int].entries@
                        .take(entry as int + 1)
                        == self.buckets@[bucket as int].entries@
                            .take(entry as int)
                            .push(self.buckets@[bucket as int].entries@[entry as int]));
                    BranchSummaryBucket::entries_map_after_push(
                        self.buckets@[bucket as int].entries@
                            .take(entry as int),
                        self.buckets@[bucket as int].entries@[entry as int],
                    );
                    assert(iau_seq_set(out@)
                        =~= Self::roots_prefix_set(self.buckets@, bucket as nat)
                            + BranchSummaryBucket::entries_map(
                                self.buckets@[bucket as int].entries@
                                    .take(entry as int + 1),
                            ).dom());
                }
                entry += 1;
            }
            proof {
                assert(self.buckets@[bucket as int].entries@
                    .take(entry as int)
                    == self.buckets@[bucket as int].entries@);
                assert(Self::roots_prefix_set(
                    self.buckets@,
                    bucket as nat + 1,
                ) =~= Self::roots_prefix_set(self.buckets@, bucket as nat)
                    + self.buckets@[bucket as int]@.dom()) by {
                    assert forall |root: AU|
                        #![trigger Self::roots_prefix_set(
                            self.buckets@,
                            bucket as nat + 1,
                        ).contains(root)]
                        Self::roots_prefix_set(
                            self.buckets@,
                            bucket as nat + 1,
                        ).contains(root)
                        == (Self::roots_prefix_set(
                            self.buckets@,
                            bucket as nat,
                        ) + self.buckets@[bucket as int]@.dom()).contains(root) by {
                    }
                }
            }
            bucket += 1;
        }
        proof {
            assert(Self::roots_prefix_set(
                self.buckets@,
                self.buckets@.len(),
            ) =~= self@.dom()) by {
                assert forall |root: AU|
                    #![trigger self@.dom().contains(root)]
                    Self::roots_prefix_set(
                        self.buckets@,
                        self.buckets@.len(),
                    ).contains(root) == self@.dom().contains(root) by {
                    if self@.contains_key(root) {
                        let selected = Self::bucket_index(
                            root,
                            self.bucket_count as nat,
                        ) as int;
                        assert(self.buckets@[selected]@.contains_key(root));
                    } else if Self::roots_prefix_set(
                        self.buckets@,
                        self.buckets@.len(),
                    ).contains(root) {
                        let selected = choose |selected: int| #![auto]
                            0 <= selected < self.buckets@.len()
                            && self.buckets@[selected]@.contains_key(root);
                        let entry = BranchSummaryBucket::entries_map_index_for_root(
                            self.buckets@[selected].entries@,
                            root,
                        );
                        assert(Self::bucket_index(
                            root,
                            self.bucket_count as nat,
                        ) == selected);
                        assert(self@.contains_key(root));
                    }
                }
            }
        }
        out
    }
}

impl View for BranchSummaryTable {
    type V = Map<AU, BranchSummaryRecordView>;

    open spec fn view(&self) -> Self::V {
        Self::buckets_map(self.buckets@, self.bucket_count as nat)
    }
}

impl BranchSummaryOwnershipImpl {
    pub open spec fn records(&self) -> Map<AU, BranchSummaryRecordView> {
        self.active@.union_prefer_right(self.retired@)
    }

    pub open spec fn all_summary_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |root: AU| #![auto]
            self.records().contains_key(root)
            && self.records()[root].summary.contains(au))
    }

    pub open spec fn active_summary_map(&self) -> Map<AU, Summary> {
        Map::new(
            |root: AU| self.active@.contains_key(root),
            |root: AU| self.active@[root].summary,
        )
    }

    pub open spec fn active_summary_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |root: AU| #![auto]
            self.active@.contains_key(root)
            && self.active@[root].summary.contains(au))
    }

    pub open spec fn persistent_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |root: AU| #![auto]
            self.records().contains_key(root)
            && self.records()[root].snapshots.persistent
            && self.records()[root].summary.contains(au))
    }

    pub open spec fn frozen_aus(&self) -> Set<AU> {
        Set::new(|au: AU| exists |root: AU| #![auto]
            self.records().contains_key(root)
            && self.records()[root].snapshots.frozen
            && self.records()[root].summary.contains(au))
    }

    pub proof fn ownership_sets_bounded(&self)
        requires self.wf(),
        ensures
            self.active_summary_aus() <= self.all_summary_aus(),
            self.persistent_aus() <= self.all_summary_aus(),
            self.frozen_aus() <= self.all_summary_aus(),
    {
        assert forall |au: AU|
            #[trigger] self.active_summary_aus().contains(au)
            implies self.all_summary_aus().contains(au) by {
            let root = choose |root: AU| #![auto]
                self.active@.contains_key(root)
                && self.active@[root].summary.contains(au);
            assert(!self.retired@.contains_key(root));
            assert(self.records().contains_key(root));
            assert(self.records()[root].summary == self.active@[root].summary);
        }
        assert forall |au: AU| #[trigger] self.persistent_aus().contains(au)
            implies self.all_summary_aus().contains(au) by { }
        assert forall |au: AU| #[trigger] self.frozen_aus().contains(au)
            implies self.all_summary_aus().contains(au) by { }
    }

    pub proof fn active_summary_map_dom(&self)
        ensures self.active_summary_map().dom() =~= self.active@.dom(),
    {
        assert forall |root: AU|
            #![trigger self.active_summary_map().dom().contains(root)]
            self.active_summary_map().dom().contains(root)
                == self.active@.dom().contains(root) by { }
    }

    pub proof fn root_record_is_owned(&self, root: AU)
        requires
            self.wf(),
            self.active@.contains_key(root)
                || self.retired@.contains_key(root),
        ensures self.all_summary_aus().contains(root),
    {
        if self.active@.contains_key(root) {
            let bucket = BranchSummaryTable::bucket_index(
                root,
                self.active.bucket_count as nat,
            ) as int;
            let index = BranchSummaryBucket::entries_map_index_for_root(
                self.active.buckets@[bucket].entries@,
                root,
            );
            assert(self.active.buckets@[bucket].entries@[index].wf());
            assert(self.active@[root].summary.contains(root));
            assert(self.records().contains_key(root));
            assert(self.records()[root] == self.active@[root]);
        } else {
            let bucket = BranchSummaryTable::bucket_index(
                root,
                self.retired.bucket_count as nat,
            ) as int;
            let index = BranchSummaryBucket::entries_map_index_for_root(
                self.retired.buckets@[bucket].entries@,
                root,
            );
            assert(self.retired.buckets@[bucket].entries@[index].wf());
            assert(self.retired@[root].summary.contains(root));
            assert(self.records().contains_key(root));
            assert(self.records()[root] == self.retired@[root]);
        }
    }

    pub proof fn active_summary_projection(&self)
        requires self.wf(),
        ensures
            self.active_summary_map().dom().finite(),
            self.active_summary_map().values().finite(),
            summary_aus(self.active_summary_map())
                =~= self.active_summary_aus(),
    {
        self.active.view_domain_finite();
        self.active_summary_map_dom();
        lemma_values_finite(self.active_summary_map());
        let values = self.active_summary_map().values();
        assert forall |au: AU|
            #[trigger] summary_aus(self.active_summary_map()).contains(au)
            implies self.active_summary_aus().contains(au) by {
            let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                values,
                au,
            );
            let root = choose |root: AU|
                self.active_summary_map().contains_key(root)
                && self.active_summary_map()[root] == summary;
            assert(self.active@.contains_key(root));
            assert(self.active@[root].summary == summary);
        }
        assert forall |au: AU|
            #[trigger] self.active_summary_aus().contains(au)
            implies summary_aus(self.active_summary_map()).contains(au) by {
            let root = choose |root: AU| #![auto]
                self.active@.contains_key(root)
                && self.active@[root].summary.contains(au);
            let summary = self.active_summary_map()[root];
            assert(self.active_summary_map().contains_key(root));
            assert(values.contains(summary));
            crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                values,
                summary,
            );
        }
    }

    pub proof fn active_summary_restrict_subset(&self, keys: Set<AU>)
        requires self.wf(),
        ensures
            summary_aus(self.active_summary_map().restrict(keys))
                <= self.active_summary_aus(),
    {
        self.active_summary_projection();
        let selected = self.active_summary_map().restrict(keys);
        crate::betree::Utils_v::lemma_subset_finite(
            self.active_summary_map().dom(),
            selected.dom(),
        );
        vstd::map_lib::lemma_values_finite(selected);
        assert forall |au: AU|
            #[trigger] summary_aus(selected).contains(au)
            implies summary_aus(self.active_summary_map()).contains(au) by {
            let summary = crate::betree::Utils_v::
                lemma_union_set_of_sets_contains(selected.values(), au);
            assert(self.active_summary_map().values().contains(summary));
            crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                self.active_summary_map().values(),
                summary,
            );
        }
    }

    pub proof fn active_roots_are_summary_aus(&self)
        requires self.wf(),
        ensures self.active_summary_map().dom()
            <= self.active_summary_aus(),
    {
        self.active_summary_map_dom();
        assert forall |root: AU|
            #[trigger] self.active_summary_map().dom().contains(root)
            implies self.active_summary_aus().contains(root) by {
            self.root_record_is_owned(root);
            assert(self.active@[root].summary.contains(root));
        }
    }


    pub fn contains_owned_au(&self, au: IAU) -> (out: bool)
        requires self.wf(),
        ensures out == self.all_summary_aus().contains(au as nat),
    {
        let active = self.active.contains_summary_au(au);
        let retired = self.retired.contains_summary_au(au);
        let out = active || retired;
        proof {
            assert(out == self.all_summary_aus().contains(au as nat)) by {
                if out {
                    if active {
                        let root = choose |root: AU| #![auto]
                            self.active@.contains_key(root)
                            && self.active@[root].summary.contains(au as nat);
                        assert(!self.retired@.contains_key(root));
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].summary.contains(au as nat));
                    } else {
                        let root = choose |root: AU| #![auto]
                            self.retired@.contains_key(root)
                            && self.retired@[root].summary.contains(au as nat);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].summary.contains(au as nat));
                    }
                } else if self.all_summary_aus().contains(au as nat) {
                    let root = choose |root: AU| #![auto]
                        self.records().contains_key(root)
                        && self.records()[root].summary.contains(au as nat);
                    if self.retired@.contains_key(root) {
                        assert(self.retired.summary_aus().contains(au as nat));
                    } else {
                        assert(self.active@.contains_key(root));
                        assert(self.active.summary_aus().contains(au as nat));
                    }
                }
            }
        }
        out
    }

    pub fn contains_root_au(&self, root_au: IAU) -> (out: bool)
        requires self.wf(),
        ensures
            out == (self.active@.contains_key(root_au as nat)
                || self.retired@.contains_key(root_au as nat)),
    {
        self.active.get_snapshots(root_au).is_some()
            || self.retired.get_snapshots(root_au).is_some()
    }

    pub open spec fn summaries_pairwise_disjoint(&self) -> bool {
        forall |left: AU, right: AU|
            #![trigger self.records().contains_key(left), self.records().contains_key(right)]
            self.records().contains_key(left)
            && self.records().contains_key(right)
            && left != right
            ==> self.records()[left].summary.disjoint(
                self.records()[right].summary,
            )
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.active.wf()
        &&& self.retired.wf()
        &&& self.active.bucket_count == self.retired.bucket_count
        &&& self.active@.dom().disjoint(self.retired@.dom())
        &&& forall |root: AU| #[trigger] self.retired@.contains_key(root)
            ==> self.retired@[root].snapshots.protected()
        &&& self.summaries_pairwise_disjoint()
    }

    proof fn record_summary_subset_all(&self, root: AU)
        requires self.records().contains_key(root),
        ensures self.records()[root].summary <= self.all_summary_aus(),
    {
        assert forall |au: AU|
            #![trigger self.records()[root].summary.contains(au)]
            self.records()[root].summary.contains(au)
            implies self.all_summary_aus().contains(au) by {
        }
    }

    pub fn new(bucket_count: u32) -> (out: Self)
        requires bucket_count > 0,
        ensures
            out.wf(),
            out.active.bucket_count == bucket_count,
            out.retired.bucket_count == bucket_count,
            out.active@ == Map::<AU, BranchSummaryRecordView>::empty(),
            out.retired@ == Map::<AU, BranchSummaryRecordView>::empty(),
            out.active_summary_map() == Map::<AU, Summary>::empty(),
            out.all_summary_aus() =~= Set::<AU>::empty(),
            out.persistent_aus() =~= Set::<AU>::empty(),
            out.frozen_aus() =~= Set::<AU>::empty(),
    {
        let active = BranchSummaryTable::new(bucket_count);
        let retired = BranchSummaryTable::new(bucket_count);
        let out = Self { active, retired };
        proof {
            assert(out.wf());
            assert(out.active@ == Map::<AU, BranchSummaryRecordView>::empty());
            assert(out.retired@ == Map::<AU, BranchSummaryRecordView>::empty());
            assert_maps_equal!(
                out.active_summary_map(),
                Map::<AU, Summary>::empty(),
                root => { }
            );
        }
        out
    }

    pub fn active_summary_aus_vec(&self) -> (out: Vec<IAU>)
        requires self.wf(),
        ensures
            unique_iau_seq(out@),
            iau_seq_set(out@) =~= self.active_summary_aus(),
    {
        proof {
            assert(self.active.summaries_pairwise_disjoint()) by {
                assert forall |left: AU, right: AU|
                    #![trigger self.active@.contains_key(left),
                        self.active@.contains_key(right)]
                    self.active@.contains_key(left)
                    && self.active@.contains_key(right)
                    && left != right
                    implies self.active@[left].summary.disjoint(
                        self.active@[right].summary,
                    ) by {
                    assert(self.records().contains_key(left));
                    assert(self.records().contains_key(right));
                    assert(self.records()[left] == self.active@[left]);
                    assert(self.records()[right] == self.active@[right]);
                }
            }
        }
        let out = self.active.flatten_summary_aus();
        proof {
            assert(self.active.summary_aus()
                =~= self.active_summary_aus()) by {
                assert forall |au: AU|
                    #![trigger self.active.summary_aus().contains(au)]
                    self.active.summary_aus().contains(au)
                    == self.active_summary_aus().contains(au) by { }
            }
        }
        out
    }

    fn add_with_membership(
        &mut self,
        root_au: IAU,
        summary: Vec<IAU>,
        snapshots: SnapshotMembership,
    ) -> (result: BranchOwnershipUpdateResult)
        requires
            old(self).wf(),
            unique_iau_seq(summary@),
            iau_seq_set(summary@).contains(root_au as nat),
            old(self).all_summary_aus().disjoint(iau_seq_set(summary@)),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==>
                !old(self).active@.contains_key(root_au as nat)
                && !old(self).retired@.contains_key(root_au as nat),
            match result {
                BranchOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.active@ == old(self).active@.insert(
                        root_au as nat,
                        BranchSummaryRecordView {
                            summary: iau_seq_set(summary@),
                            snapshots,
                        },
                    )
                    &&& self.retired@ == old(self).retired@
                    &&& self.all_summary_aus()
                        =~= old(self).all_summary_aus() + iau_seq_set(summary@)
                    &&& self.active_summary_aus()
                        =~= old(self).active_summary_aus() + iau_seq_set(summary@)
                    &&& self.active_summary_map()
                        == old(self).active_summary_map().insert(
                            root_au as nat,
                            iau_seq_set(summary@),
                        )
                    &&& self.persistent_aus()
                        =~= old(self).persistent_aus()
                            + if snapshots.persistent {
                                iau_seq_set(summary@)
                            } else {
                                Set::<AU>::empty()
                            }
                    &&& self.frozen_aus()
                        =~= old(self).frozen_aus()
                            + if snapshots.frozen {
                                iau_seq_set(summary@)
                            } else {
                                Set::<AU>::empty()
                            }
                },
                BranchOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                    &&& self.active.bucket_count == old(self).active.bucket_count
                    &&& self.retired.bucket_count == old(self).retired.bucket_count
                },
            },
    {
        let active = self.active.get_snapshots(root_au);
        let retired = self.retired.get_snapshots(root_au);
        if active.is_some() || retired.is_some() {
            return BranchOwnershipUpdateResult::Noop;
        }
        let ghost summary_set = iau_seq_set(summary@);
        let record = BranchSummaryRecord { root_au, summary, snapshots };
        self.active.insert(record);
        proof {
            assert(self.records() == old(self).records().insert(
                root_au as nat,
                BranchSummaryRecordView {
                    summary: summary_set,
                    snapshots,
                },
            )) by {
                assert_maps_equal!(
                    self.records(),
                    old(self).records().insert(
                        root_au as nat,
                        BranchSummaryRecordView {
                            summary: summary_set,
                            snapshots,
                        },
                    ),
                    root => { }
                );
            }
            assert(self.all_summary_aus()
                =~= old(self).all_summary_aus() + summary_set) by {
                assert forall |au: AU|
                    #![trigger self.all_summary_aus().contains(au)]
                    self.all_summary_aus().contains(au)
                    == (old(self).all_summary_aus() + summary_set)
                        .contains(au) by {
                    if self.all_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].summary.contains(au);
                        if root == root_au as nat {
                            assert(summary_set.contains(au));
                        } else {
                            assert(old(self).records().contains_key(root));
                            assert(old(self).records()[root].summary.contains(au));
                            assert(old(self).all_summary_aus().contains(au));
                        }
                    } else if old(self).all_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            old(self).records().contains_key(root)
                            && old(self).records()[root].summary.contains(au);
                        assert(root != root_au as nat);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].summary.contains(au));
                        assert(self.all_summary_aus().contains(au));
                    } else if summary_set.contains(au) {
                        assert(self.records().contains_key(root_au as nat));
                        assert(self.records()[root_au as nat].summary.contains(au));
                        assert(self.all_summary_aus().contains(au));
                    }
                }
            }
            assert(self.active_summary_aus()
                =~= old(self).active_summary_aus() + summary_set) by {
                assert forall |au: AU|
                    #![trigger self.active_summary_aus().contains(au)]
                    self.active_summary_aus().contains(au)
                    == (old(self).active_summary_aus() + summary_set)
                        .contains(au) by {
                    if self.active_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.active@.contains_key(root)
                            && self.active@[root].summary.contains(au);
                        if root == root_au as nat {
                            assert(summary_set.contains(au));
                        } else {
                            assert(old(self).active@.contains_key(root));
                            assert(old(self).active@[root].summary.contains(au));
                            assert(old(self).active_summary_aus().contains(au));
                        }
                    } else if old(self).active_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            old(self).active@.contains_key(root)
                            && old(self).active@[root].summary.contains(au);
                        assert(root != root_au as nat);
                        assert(self.active@.contains_key(root));
                        assert(self.active@[root].summary.contains(au));
                        assert(self.active_summary_aus().contains(au));
                    } else if summary_set.contains(au) {
                        assert(self.active@.contains_key(root_au as nat));
                        assert(self.active@[root_au as nat].summary.contains(au));
                        assert(self.active_summary_aus().contains(au));
                    }
                }
            }
            assert(self.wf()) by {
                assert(self.summaries_pairwise_disjoint()) by {
                    assert forall |left: AU, right: AU|
                        #![trigger self.records().contains_key(left), self.records().contains_key(right)]
                        self.records().contains_key(left)
                        && self.records().contains_key(right)
                        && left != right
                        implies self.records()[left].summary.disjoint(
                            self.records()[right].summary,
                        ) by {
                        if left == root_au as nat {
                            assert(old(self).records().contains_key(right));
                            assert forall |au: AU|
                                #![trigger self.records()[left].summary.contains(au)]
                                self.records()[left].summary.contains(au)
                                implies !self.records()[right].summary.contains(au) by {
                                if self.records()[right].summary.contains(au) {
                                    assert(old(self).all_summary_aus().contains(au));
                                    assert(summary_set.contains(au));
                                }
                            }
                        } else if right == root_au as nat {
                            assert(old(self).records().contains_key(left));
                            assert forall |au: AU|
                                #![trigger self.records()[left].summary.contains(au)]
                                self.records()[left].summary.contains(au)
                                implies !self.records()[right].summary.contains(au) by {
                                if self.records()[right].summary.contains(au) {
                                    assert(old(self).all_summary_aus().contains(au));
                                    assert(summary_set.contains(au));
                                }
                            }
                        } else {
                            assert(old(self).records().contains_key(left));
                            assert(old(self).records().contains_key(right));
                            assert(old(self).records()[left].summary.disjoint(
                                old(self).records()[right].summary,
                            ));
                        }
                    }
                }
            }
            assert(self.persistent_aus()
                =~= old(self).persistent_aus()
                    + if snapshots.persistent {
                        summary_set
                    } else {
                        Set::<AU>::empty()
                    }) by {
                assert forall |au: AU|
                    #![trigger self.persistent_aus().contains(au)]
                    self.persistent_aus().contains(au)
                    == (old(self).persistent_aus()
                        + if snapshots.persistent {
                            summary_set
                        } else {
                            Set::<AU>::empty()
                        }).contains(au) by {
                    if self.persistent_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].snapshots.persistent
                            && self.records()[root].summary.contains(au);
                        if root != root_au as nat {
                            assert(old(self).persistent_aus().contains(au));
                        }
                    } else if (old(self).persistent_aus()
                        + if snapshots.persistent {
                            summary_set
                        } else {
                            Set::<AU>::empty()
                        }).contains(au)
                    {
                        if old(self).persistent_aus().contains(au) {
                            let root = choose |root: AU| #![auto]
                                old(self).records().contains_key(root)
                                && old(self).records()[root].snapshots.persistent
                                && old(self).records()[root].summary.contains(au);
                            assert(self.records().contains_key(root));
                            assert(self.records()[root] == old(self).records()[root]);
                            assert(exists |candidate: AU| #![auto]
                                self.records().contains_key(candidate)
                                && self.records()[candidate].snapshots.persistent
                                && self.records()[candidate].summary.contains(au));
                            assert(self.persistent_aus().contains(au));
                        } else {
                            assert(snapshots.persistent);
                            assert(summary_set.contains(au));
                            assert(self.records().contains_key(root_au as nat));
                            assert(exists |candidate: AU| #![auto]
                                self.records().contains_key(candidate)
                                && self.records()[candidate].snapshots.persistent
                                && self.records()[candidate].summary.contains(au));
                            assert(self.persistent_aus().contains(au));
                        }
                    }
                }
            }
            assert(self.frozen_aus()
                =~= old(self).frozen_aus()
                    + if snapshots.frozen {
                        summary_set
                    } else {
                        Set::<AU>::empty()
                    }) by {
                assert forall |au: AU|
                    #![trigger self.frozen_aus().contains(au)]
                    self.frozen_aus().contains(au)
                    == (old(self).frozen_aus()
                        + if snapshots.frozen {
                            summary_set
                        } else {
                            Set::<AU>::empty()
                        }).contains(au) by {
                    if self.frozen_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].snapshots.frozen
                            && self.records()[root].summary.contains(au);
                        if root != root_au as nat {
                            assert(old(self).frozen_aus().contains(au));
                        }
                    } else if (old(self).frozen_aus()
                        + if snapshots.frozen {
                            summary_set
                        } else {
                            Set::<AU>::empty()
                        }).contains(au)
                    {
                        if old(self).frozen_aus().contains(au) {
                            let root = choose |root: AU| #![auto]
                                old(self).records().contains_key(root)
                                && old(self).records()[root].snapshots.frozen
                                && old(self).records()[root].summary.contains(au);
                            assert(self.records().contains_key(root));
                            assert(self.records()[root] == old(self).records()[root]);
                            assert(exists |candidate: AU| #![auto]
                                self.records().contains_key(candidate)
                                && self.records()[candidate].snapshots.frozen
                                && self.records()[candidate].summary.contains(au));
                            assert(self.frozen_aus().contains(au));
                        } else {
                            assert(snapshots.frozen);
                            assert(summary_set.contains(au));
                            assert(self.records().contains_key(root_au as nat));
                            assert(exists |candidate: AU| #![auto]
                                self.records().contains_key(candidate)
                                && self.records()[candidate].snapshots.frozen
                                && self.records()[candidate].summary.contains(au));
                            assert(self.frozen_aus().contains(au));
                        }
                    }
                }
            }
            assert_maps_equal!(
                self.active_summary_map(),
                old(self).active_summary_map().insert(root_au as nat, summary_set),
                root => { }
            );
        }
        BranchOwnershipUpdateResult::Applied { reclaimed: Vec::new() }
    }

    pub fn add_ephemeral(
        &mut self,
        root_au: IAU,
        summary: Vec<IAU>,
    ) -> (result: BranchOwnershipUpdateResult)
        requires
            old(self).wf(),
            unique_iau_seq(summary@),
            iau_seq_set(summary@).contains(root_au as nat),
            old(self).all_summary_aus().disjoint(iau_seq_set(summary@)),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==>
                !old(self).active@.contains_key(root_au as nat)
                && !old(self).retired@.contains_key(root_au as nat),
            match result {
                BranchOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.retired@ == old(self).retired@
                    &&& self.all_summary_aus()
                        =~= old(self).all_summary_aus() + iau_seq_set(summary@)
                    &&& self.active_summary_aus()
                        =~= old(self).active_summary_aus() + iau_seq_set(summary@)
                    &&& self.active_summary_map()
                        == old(self).active_summary_map().insert(
                            root_au as nat,
                            iau_seq_set(summary@),
                        )
                    &&& self.persistent_aus() =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BranchOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                },
            },
    {
        let snapshots = SnapshotMembership::ephemeral();
        self.add_with_membership(root_au, summary, snapshots)
    }

    pub fn add_recovered(
        &mut self,
        root_au: IAU,
        summary: Vec<IAU>,
    ) -> (result: BranchOwnershipUpdateResult)
        requires
            old(self).wf(),
            unique_iau_seq(summary@),
            iau_seq_set(summary@).contains(root_au as nat),
            old(self).all_summary_aus().disjoint(iau_seq_set(summary@)),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==>
                !old(self).active@.contains_key(root_au as nat)
                && !old(self).retired@.contains_key(root_au as nat),
            match result {
                BranchOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.retired@ == old(self).retired@
                    &&& self.all_summary_aus()
                        =~= old(self).all_summary_aus() + iau_seq_set(summary@)
                    &&& self.active_summary_aus()
                        =~= old(self).active_summary_aus() + iau_seq_set(summary@)
                    &&& self.active_summary_map()
                        == old(self).active_summary_map().insert(
                            root_au as nat,
                            iau_seq_set(summary@),
                        )
                    &&& self.persistent_aus()
                        =~= old(self).persistent_aus() + iau_seq_set(summary@)
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BranchOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                },
            },
    {
        let snapshots = SnapshotMembership::recovered();
        self.add_with_membership(root_au, summary, snapshots)
    }

    pub fn retire(
        &mut self,
        root_au: IAU,
    ) -> (result: BranchOwnershipUpdateResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==> old(self).active@.contains_key(root_au as nat),
            (result is Applied) ==> self.all_summary_aus()
                =~= if old(self).active@[root_au as nat]
                    .snapshots.unprotected()
                {
                    old(self).all_summary_aus()
                        - old(self).active@[root_au as nat].summary
                } else {
                    old(self).all_summary_aus()
                },
            match result {
                BranchOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& self.active_summary_map()
                        == old(self).active_summary_map().remove(root_au as nat)
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@)
                        =~= if old(self).active@[root_au as nat]
                            .snapshots.unprotected()
                        {
                            old(self).active@[root_au as nat].summary
                        } else {
                            Set::<AU>::empty()
                        }
                    &&& self.persistent_aus() =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BranchOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                },
            },
    {
        let present = self.active.get_snapshots(root_au);
        if present.is_none() {
            return BranchOwnershipUpdateResult::Noop;
        }
        let ghost initial_retired = self.retired@;
        let record = self.active.take(root_au);
        proof { assert(record is Some); }
        let record = record.unwrap();
        if record.snapshots.persistent || record.snapshots.frozen {
            let ghost record_view = record@;
            proof {
                assert(self.retired@ == initial_retired);
                assert(initial_retired == old(self).retired@);
                assert(record.root_au == root_au);
                assert(old(self).active@.contains_key(root_au as nat));
                assert(!old(self).retired@.contains_key(root_au as nat));
                assert(!self.retired@.contains_key(root_au as nat));
            }
            self.retired.insert(record);
            proof {
                assert(self.records() == old(self).records()) by {
                    assert_maps_equal!(self.records(), old(self).records(), root => {
                        if root == root_au as nat {
                            assert(self.retired@.contains_key(root));
                            assert(self.retired@[root] == record_view);
                            assert(old(self).active@[root] == record_view);
                        }
                    });
                }
                assert(self.summaries_pairwise_disjoint()) by {
                    assert forall |left: AU, right: AU|
                        #![trigger self.records().contains_key(left), self.records().contains_key(right)]
                        self.records().contains_key(left)
                        && self.records().contains_key(right)
                        && left != right
                        implies self.records()[left].summary.disjoint(
                            self.records()[right].summary,
                        ) by {
                        assert(old(self).records()[left].summary.disjoint(
                            old(self).records()[right].summary,
                        ));
                    }
                }
                assert(self.wf());
                assert(self.all_summary_aus()
                    =~= old(self).all_summary_aus()) by {
                    assert forall |au: AU|
                        #![trigger self.all_summary_aus().contains(au)]
                        self.all_summary_aus().contains(au)
                            == old(self).all_summary_aus().contains(au) by { }
                }
                assert(self.persistent_aus() =~= old(self).persistent_aus()) by {
                    assert forall |au: AU|
                        #![trigger self.persistent_aus().contains(au)]
                        self.persistent_aus().contains(au)
                        == old(self).persistent_aus().contains(au) by { }
                }
                assert(self.frozen_aus() =~= old(self).frozen_aus()) by {
                    assert forall |au: AU|
                        #![trigger self.frozen_aus().contains(au)]
                        self.frozen_aus().contains(au)
                        == old(self).frozen_aus().contains(au) by { }
                }
                assert_maps_equal!(
                    self.active_summary_map(),
                    old(self).active_summary_map().remove(root_au as nat),
                    root => { }
                );
            }
            BranchOwnershipUpdateResult::Applied { reclaimed: Vec::new() }
        } else {
            let ghost record_view = record@;
            let reclaimed = record.summary;
            proof {
                assert(iau_seq_set(reclaimed@) == record_view.summary);
                assert(self.records() == old(self).records().remove(root_au as nat)) by {
                    assert_maps_equal!(
                        self.records(),
                        old(self).records().remove(root_au as nat),
                        root => { }
                    );
                }
                assert(self.summaries_pairwise_disjoint()) by {
                    assert forall |left: AU, right: AU|
                        #![trigger self.records().contains_key(left), self.records().contains_key(right)]
                        self.records().contains_key(left)
                        && self.records().contains_key(right)
                        && left != right
                        implies self.records()[left].summary.disjoint(
                            self.records()[right].summary,
                        ) by {
                        assert(old(self).records()[left].summary.disjoint(
                            old(self).records()[right].summary,
                        ));
                    }
                }
                assert(self.wf());
                assert(unique_iau_seq(reclaimed@));
                assert(self.all_summary_aus()
                    =~= old(self).all_summary_aus() - record_view.summary) by {
                    assert forall |au: AU|
                        #![trigger self.all_summary_aus().contains(au)]
                        self.all_summary_aus().contains(au)
                        == (old(self).all_summary_aus() - record_view.summary)
                            .contains(au) by {
                        if self.all_summary_aus().contains(au) {
                            let owner = choose |owner: AU| #![auto]
                                self.records().contains_key(owner)
                                && self.records()[owner].summary.contains(au);
                            assert(old(self).records().contains_key(owner));
                            assert(old(self).records()[owner].summary.contains(au));
                            assert(old(self).all_summary_aus().contains(au));
                            assert(owner != root_au as nat);
                            assert(!record_view.summary.contains(au)) by {
                                if record_view.summary.contains(au) {
                                    assert(old(self).records()
                                        .contains_key(root_au as nat));
                                    assert(old(self).records().contains_key(owner));
                                    assert(old(self).summaries_pairwise_disjoint());
                                    assert(old(self).records()[root_au as nat]
                                        .summary.disjoint(
                                            old(self).records()[owner].summary,
                                        ));
                                    assert(!old(self).records()[owner]
                                        .summary.contains(au));
                                }
                            }
                        } else if (old(self).all_summary_aus()
                            - record_view.summary).contains(au)
                        {
                            let owner = choose |owner: AU| #![auto]
                                old(self).records().contains_key(owner)
                                && old(self).records()[owner].summary.contains(au);
                            assert(owner != root_au as nat);
                            assert(self.records().contains_key(owner));
                            assert(self.records()[owner].summary.contains(au));
                            assert(self.all_summary_aus().contains(au));
                        }
                    }
                }
                assert(self.persistent_aus() =~= old(self).persistent_aus());
                assert(self.frozen_aus() =~= old(self).frozen_aus());
                assert_maps_equal!(
                    self.active_summary_map(),
                    old(self).active_summary_map().remove(root_au as nat),
                    root => { }
                );
            }
            BranchOwnershipUpdateResult::Applied { reclaimed }
        }
    }

    pub fn retire_many(
        &mut self,
        roots: &Vec<IAU>,
    ) -> (result: BranchOwnershipUpdateResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            (result is Applied) <==> branch_batch_retire_applicable(
                *old(self),
                roots@,
            ),
            match result {
                BranchOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& self.active_summary_map()
                        == old(self).active_summary_map().remove_keys(
                            iau_seq_set(roots@),
                        )
                    &&& self.all_summary_aus()
                        <= old(self).all_summary_aus()
                    &&& self.persistent_aus() =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@)
                        =~= old(self).all_summary_aus()
                            - self.all_summary_aus()
                    &&& iau_seq_set(reclaimed@)
                        <= old(self).all_summary_aus()
                            - self.all_summary_aus()
                    &&& iau_seq_set(reclaimed@) <= summary_aus(
                        old(self).active_summary_map().restrict(
                            iau_seq_set(roots@),
                        ),
                    )
                },
                BranchOwnershipUpdateResult::Noop => {
                    &&& self.active.buckets@ == old(self).active.buckets@
                    &&& self.retired.buckets@ == old(self).retired.buckets@
                },
            },
    {
        let ghost initial_active = self.active_summary_map();
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();
        let active_bucket_count = self.active.bucket_count;
        let retired_bucket_count = self.retired.bucket_count;
        proof { self.active_summary_projection(); }

        if !iau_vec_unique(roots) {
            return BranchOwnershipUpdateResult::Noop;
        }
        let mut check = 0usize;
        while check < roots.len()
            invariant
                self.wf(),
                self.active_summary_map() == initial_active,
                self.persistent_aus() == initial_persistent,
                self.frozen_aus() == initial_frozen,
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                check <= roots.len(),
                forall |i: int| 0 <= i < check
                    ==> initial_active.contains_key(
                        (#[trigger] roots@[i]) as nat,
                    ),
            decreases roots.len() - check,
        {
            let present = self.active.get_snapshots(roots[check]);
            if present.is_none() {
                proof {
                    assert(!self.active@.contains_key(
                        roots@[check as int] as nat,
                    ));
                    assert(!initial_active.contains_key(
                        roots@[check as int] as nat,
                    ));
                    assert(iau_seq_set(roots@).contains(
                        roots@[check as int] as nat,
                    )) by {
                        assert(exists |i: int| 0 <= i < roots@.len()
                            && roots@[i] as nat
                                == roots@[check as int] as nat) by {
                            assert(check < roots.len());
                        }
                    }
                    assert(!(iau_seq_set(roots@)
                        <= initial_active.dom()));
                }
                return BranchOwnershipUpdateResult::Noop;
            }
            proof {
                assert(initial_active.contains_key(
                    roots@[check as int] as nat,
                ));
            }
            check += 1;
        }

        let mut reclaimed = Vec::<IAU>::new();
        let mut index = 0usize;
        while index < roots.len()
            invariant
                self.wf(),
                unique_iau_seq(roots@),
                index <= roots.len(),
                self.active_summary_map()
                    == initial_active.remove_keys(
                        iau_seq_set(roots@.take(index as int)),
                    ),
                self.persistent_aus() =~= initial_persistent,
                self.frozen_aus() =~= initial_frozen,
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                self.all_summary_aus() <= old(self).all_summary_aus(),
                unique_iau_seq(reclaimed@),
                iau_seq_set(reclaimed@)
                    =~= old(self).all_summary_aus()
                        - self.all_summary_aus(),
                forall |au: AU|
                    #[trigger] iau_seq_set(reclaimed@).contains(au)
                    ==> exists |i: int| 0 <= i < index
                        && initial_active[roots@[i] as nat].contains(au),
            decreases roots.len() - index,
        {
            let root = roots[index];
            let ghost before_reclaimed = reclaimed@;
            let ghost before_reclaimed_set = iau_seq_set(reclaimed@);
            let ghost selected_summary = initial_active[root as nat];
            let ghost before_all = self.all_summary_aus();
            let ghost selected_record = self.active@[root as nat];
            proof {
                assert(initial_active.contains_key(root as nat));
                assert(!iau_seq_set(roots@.take(index as int))
                    .contains(root as nat)) by {
                    if iau_seq_set(roots@.take(index as int))
                        .contains(root as nat)
                    {
                        let earlier = choose |i: int| #![auto]
                            0 <= i < index && roots@[i] == root;
                        assert(earlier != index);
                    }
                }
                assert(self.active_summary_map().contains_key(root as nat));
                assert(self.active_summary_map()[root as nat]
                    == initial_active[root as nat]);
                assert(self.active_summary_map()[root as nat]
                    == self.active@[root as nat].summary);
                assert(selected_record.summary =~= selected_summary);
                self.ownership_sets_bounded();
                assert(selected_summary <= before_all) by {
                    assert forall |au: AU|
                        #[trigger] selected_summary.contains(au)
                        implies before_all.contains(au) by {
                        assert(self.active_summary_aus().contains(au)) by {
                            assert(exists |candidate: AU| #![auto]
                                self.active@.contains_key(candidate)
                                && self.active@[candidate].summary
                                    .contains(au)) by {
                                assert(self.active@[root as nat].summary
                                    .contains(au));
                            }
                        }
                    }
                }
            }
            let retired = self.retire(root);
            let newly_reclaimed = match retired {
                BranchOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
                BranchOwnershipUpdateResult::Noop => {
                    proof { assert(false); }
                    return BranchOwnershipUpdateResult::Noop;
                },
            };
            proof {
                assert(iau_seq_set(newly_reclaimed@)
                    =~= if selected_record.snapshots.unprotected() {
                        selected_summary
                    } else {
                        Set::<AU>::empty()
                    });
                assert(self.all_summary_aus()
                    =~= if selected_record.snapshots.unprotected() {
                        before_all - selected_summary
                    } else {
                        before_all
                    });
                assert(iau_seq_set(newly_reclaimed@)
                    <= before_all - self.all_summary_aus()) by {
                    assert forall |au: AU|
                        #[trigger] iau_seq_set(newly_reclaimed@).contains(au)
                        implies before_all.contains(au)
                            && !self.all_summary_aus().contains(au) by {
                        if selected_record.snapshots.unprotected() {
                            assert(selected_summary.contains(au));
                            assert((before_all - selected_summary)
                                =~= self.all_summary_aus());
                        } else {
                            assert(!iau_seq_set(newly_reclaimed@)
                                .contains(au));
                        }
                    }
                }
                assert(before_reclaimed_set.disjoint(
                    iau_seq_set(newly_reclaimed@),
                )) by {
                    assert forall |au: AU|
                        #[trigger] before_reclaimed_set.contains(au)
                        implies !iau_seq_set(newly_reclaimed@).contains(au) by {
                        if iau_seq_set(newly_reclaimed@).contains(au) {
                            assert(before_all.contains(au));
                            assert(before_reclaimed_set
                                <= old(self).all_summary_aus() - before_all);
                        }
                    }
                }
            }
            append_unique_aus(&mut reclaimed, newly_reclaimed);
            proof {
                assert(iau_seq_set(reclaimed@)
                    =~= before_reclaimed_set
                        + iau_seq_set(newly_reclaimed@));
                assert(roots@.take(index as int + 1)
                    == roots@.take(index as int).push(root));
                iau_seq_set_push(roots@.take(index as int), root);
                assert(self.active_summary_map()
                    == initial_active.remove_keys(
                        iau_seq_set(roots@.take(index as int + 1)),
                    )) by {
                    assert_maps_equal!(
                        self.active_summary_map(),
                        initial_active.remove_keys(
                            iau_seq_set(roots@.take(index as int + 1)),
                        ),
                        candidate => {}
                    );
                }
                assert_sets_equal!(
                    iau_seq_set(reclaimed@),
                    old(self).all_summary_aus()
                        - self.all_summary_aus(),
                    au => {
                    assert(self.all_summary_aus() <= before_all) by {
                        assert forall |au: AU|
                            #[trigger] self.all_summary_aus().contains(au)
                            implies before_all.contains(au) by {
                            }
                    }
                    if iau_seq_set(reclaimed@).contains(au) {
                        if before_reclaimed_set.contains(au) {
                            assert(!before_all.contains(au));
                            assert(!self.all_summary_aus().contains(au));
                        } else {
                            assert(iau_seq_set(newly_reclaimed@).contains(au));
                            assert(before_all.contains(au));
                            assert(!self.all_summary_aus().contains(au));
                        }
                    } else if old(self).all_summary_aus().contains(au)
                        && !self.all_summary_aus().contains(au)
                    {
                        if !before_all.contains(au) {
                            assert(before_reclaimed_set.contains(au));
                        } else {
                            assert(selected_record.snapshots.unprotected());
                            assert(selected_summary.contains(au));
                            assert(iau_seq_set(newly_reclaimed@).contains(au));
                        }
                    }
                });
                assert forall |au: AU|
                    #[trigger] iau_seq_set(reclaimed@).contains(au)
                    implies exists |i: int| 0 <= i < index + 1
                        && initial_active[roots@[i] as nat].contains(au) by {
                    if before_reclaimed_set.contains(au) {
                        let i = choose |i: int| 0 <= i < index
                            && initial_active[roots@[i] as nat].contains(au);
                        assert(0 <= i < index + 1);
                    } else {
                        assert(iau_seq_set(newly_reclaimed@).contains(au));
                        assert(selected_summary.contains(au));
                        assert(initial_active[roots@[index as int] as nat]
                            .contains(au));
                    }
                }
            }
            index += 1;
        }
        proof {
            assert(roots@.take(index as int) == roots@);
            let ghost selected = initial_active.restrict(iau_seq_set(roots@));
            assert(initial_active.dom().finite());
            crate::betree::Utils_v::lemma_subset_finite(
                initial_active.dom(),
                selected.dom(),
            );
            vstd::map_lib::lemma_values_finite(selected);
            assert forall |au: AU|
                #[trigger] iau_seq_set(reclaimed@).contains(au)
                implies summary_aus(selected).contains(au) by {
                let i = choose |i: int| 0 <= i < roots@.len()
                    && initial_active[roots@[i] as nat].contains(au);
                assert(iau_seq_set(roots@).contains(roots@[i] as nat));
                assert(selected.contains_key(roots@[i] as nat));
                assert(selected[roots@[i] as nat]
                    == initial_active[roots@[i] as nat]);
                assert(selected.values().contains(
                    initial_active[roots@[i] as nat],
                ));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    selected.values(),
                    initial_active[roots@[i] as nat],
                );
            }
        }
        BranchOwnershipUpdateResult::Applied { reclaimed }
    }

    pub proof fn retire_many_reclaimed_exact(
        pre: Self,
        post: Self,
        roots: Seq<IAU>,
        reclaimed: Seq<IAU>,
    )
        requires
            pre.wf(),
            post.wf(),
            post.active_summary_map()
                == pre.active_summary_map().remove_keys(
                    iau_seq_set(roots),
                ),
            post.persistent_aus() =~= pre.persistent_aus(),
            post.frozen_aus() =~= pre.frozen_aus(),
            iau_seq_set(reclaimed)
                =~= pre.all_summary_aus() - post.all_summary_aus(),
            iau_seq_set(reclaimed) <= summary_aus(
                pre.active_summary_map().restrict(iau_seq_set(roots)),
            ),
        ensures
            iau_seq_set(reclaimed) =~= summary_aus(
                pre.active_summary_map().restrict(iau_seq_set(roots)),
            ) - pre.persistent_aus() - pre.frozen_aus(),
    {
        let selected = pre.active_summary_map().restrict(
            iau_seq_set(roots),
        );
        pre.active_summary_projection();
        pre.ownership_sets_bounded();
        post.active_summary_projection();
        post.ownership_sets_bounded();
        assert(selected.dom() <= pre.active_summary_map().dom());
        crate::betree::Utils_v::lemma_subset_finite(
            pre.active_summary_map().dom(),
            selected.dom(),
        );
        vstd::map_lib::lemma_values_finite(selected);
        assert_sets_equal!(
            iau_seq_set(reclaimed),
            summary_aus(selected)
                - pre.persistent_aus()
                - pre.frozen_aus(),
            au => {
                if iau_seq_set(reclaimed).contains(au) {
                    assert(summary_aus(selected).contains(au));
                    assert(!post.all_summary_aus().contains(au));
                    if pre.persistent_aus().contains(au) {
                        assert(post.persistent_aus().contains(au));
                        assert(post.all_summary_aus().contains(au));
                    }
                    if pre.frozen_aus().contains(au) {
                        assert(post.frozen_aus().contains(au));
                        assert(post.all_summary_aus().contains(au));
                    }
                } else if summary_aus(selected).contains(au)
                    && !pre.persistent_aus().contains(au)
                    && !pre.frozen_aus().contains(au)
                {
                    let selected_summary =
                        crate::betree::Utils_v::
                            lemma_union_set_of_sets_contains(
                                selected.values(),
                                au,
                            );
                    let selected_root = choose |root: AU|
                        selected.contains_key(root)
                            && selected[root] == selected_summary;
                    assert(pre.active@.contains_key(selected_root));
                    assert(pre.active@[selected_root].summary
                        == selected_summary);
                    assert(pre.records().contains_key(selected_root));
                    assert(pre.records()[selected_root]
                        == pre.active@[selected_root]);
                    assert(iau_seq_set(roots).contains(selected_root));

                    if post.all_summary_aus().contains(au) {
                        let post_root = choose |root: AU| #![auto]
                            post.records().contains_key(root)
                                && post.records()[root].summary.contains(au);
                        if post.active@.contains_key(post_root) {
                            assert(post.active_summary_map()
                                .contains_key(post_root));
                            assert(pre.active_summary_map()
                                .contains_key(post_root));
                            assert(!iau_seq_set(roots).contains(post_root));
                            assert(post.active_summary_map()[post_root]
                                == post.active@[post_root].summary);
                            assert(pre.active_summary_map()[post_root]
                                == post.active_summary_map()[post_root]);
                            assert(pre.active_summary_map()[post_root]
                                == pre.active@[post_root].summary);
                            assert(pre.active@[post_root].summary
                                .contains(au));
                            if post_root != selected_root {
                                assert(pre.summaries_pairwise_disjoint());
                                assert(pre.records().contains_key(post_root));
                                assert(pre.records()[post_root]
                                    == pre.active@[post_root]);
                                assert(pre.records()[selected_root].summary
                                    .disjoint(
                                        pre.records()[post_root].summary,
                                    ));
                            } else {
                                assert(false);
                            }
                        } else {
                            assert(post.retired@.contains_key(post_root));
                            assert(post.retired@[post_root]
                                .snapshots.protected());
                            if post.retired@[post_root]
                                .snapshots.persistent
                            {
                                assert(post.persistent_aus().contains(au));
                                assert(pre.persistent_aus().contains(au));
                            } else {
                                assert(post.retired@[post_root]
                                    .snapshots.frozen);
                                assert(post.frozen_aus().contains(au));
                                assert(pre.frozen_aus().contains(au));
                            }
                        }
                    }
                    assert(!post.all_summary_aus().contains(au));
                    assert(pre.active_summary_aus().contains(au));
                    assert(pre.all_summary_aus().contains(au));
                    assert(iau_seq_set(reclaimed).contains(au));
                }
            }
        );
    }

    pub fn freeze_current(&mut self)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.active.bucket_count == old(self).active.bucket_count,
            self.retired.bucket_count == old(self).retired.bucket_count,
            self.all_summary_aus() =~= old(self).all_summary_aus(),
            self.active_summary_map() == old(self).active_summary_map(),
            self.active_summary_aus() =~= old(self).active_summary_aus(),
            self.persistent_aus() =~= old(self).persistent_aus(),
            self.frozen_aus()
                =~= old(self).frozen_aus() + old(self).active_summary_aus(),
    {
        let active_bucket_count = self.active.bucket_count;
        let retired_bucket_count = self.retired.bucket_count;
        let roots = self.active.roots();
        let ghost initial_active = self.active@;
        let ghost initial_retired = self.retired@;
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();
        let ghost initial_active_summary_aus = self.active_summary_aus();
        let mut index = 0usize;
        while index < roots.len()
            invariant
                self.wf(),
                self.active.bucket_count == active_bucket_count,
                self.retired.bucket_count == retired_bucket_count,
                unique_iau_seq(roots@),
                iau_seq_set(roots@) =~= initial_active.dom(),
                index <= roots.len(),
                self.retired@ == initial_retired,
                self.active@
                    == freeze_branch_selected(
                        initial_active,
                        iau_seq_set(roots@.take(index as int)),
                    ),
            decreases roots.len() - index,
        {
            let root = roots[index];
            let snapshots = self.active.get_snapshots(root);
            proof {
                assert(initial_active.contains_key(root as nat));
                assert(snapshots is Some);
                assert(!iau_seq_set(roots@.take(index as int))
                    .contains(root as nat)) by {
                    if iau_seq_set(roots@.take(index as int))
                        .contains(root as nat)
                    {
                        let earlier = choose |i: int| #![auto]
                            0 <= i < roots@.take(index as int).len()
                            && roots@.take(index as int)[i] == root;
                        assert(roots@[earlier] == roots@[index as int]);
                        assert(earlier != index);
                    }
                }
                assert(snapshots.unwrap() == initial_active[root as nat].snapshots);
            }
            let mut snapshots = snapshots.unwrap();
            snapshots.mark_frozen();
            self.active.set_snapshots(root, snapshots);
            proof {
                let ghost selected = iau_seq_set(roots@.take(index as int));
                freeze_branch_selected_insert(
                    initial_active,
                    selected,
                    root as nat,
                );
                assert(roots@.take(index as int + 1)
                    == roots@.take(index as int).push(root));
                iau_seq_set_push(roots@.take(index as int), root);
                assert(self.active@
                    == freeze_branch_selected(
                        initial_active,
                        iau_seq_set(roots@.take(index as int + 1)),
                    ));
                assert(self.records().dom()
                    == old(self).records().dom());
                assert(self.summaries_pairwise_disjoint()) by {
                    assert forall |left: AU, right: AU|
                        #![trigger self.records().contains_key(left), self.records().contains_key(right)]
                        self.records().contains_key(left)
                        && self.records().contains_key(right)
                        && left != right
                        implies self.records()[left].summary.disjoint(
                            self.records()[right].summary,
                        ) by {
                        assert(self.records()[left].summary
                            == old(self).records()[left].summary);
                        assert(self.records()[right].summary
                            == old(self).records()[right].summary);
                        assert(old(self).records()[left].summary.disjoint(
                            old(self).records()[right].summary,
                        ));
                    }
                }
                assert(self.wf());
            }
            index += 1;
        }
        proof {
            assert(self.active.bucket_count == active_bucket_count);
            assert(self.retired.bucket_count == retired_bucket_count);
            assert(roots@.take(index as int) == roots@);
            assert(iau_seq_set(roots@) =~= initial_active.dom());
            assert(self.records().dom()
                == initial_active.dom() + initial_retired.dom());
            assert forall |root: AU| #![trigger self.records().contains_key(root)]
                self.records().contains_key(root)
                implies {
                    &&& (initial_active.contains_key(root)
                        || initial_retired.contains_key(root))
                    &&& self.records()[root].summary
                        == if initial_active.contains_key(root) {
                            initial_active[root].summary
                        } else {
                            initial_retired[root].summary
                        }
                    &&& self.records()[root].snapshots.persistent
                        == if initial_active.contains_key(root) {
                            initial_active[root].snapshots.persistent
                        } else {
                            initial_retired[root].snapshots.persistent
                        }
                    &&& self.records()[root].snapshots.frozen
                        == if initial_active.contains_key(root) {
                            true
                        } else {
                            initial_retired[root].snapshots.frozen
                        }
                } by { }
            assert(self.all_summary_aus()
                =~= old(self).all_summary_aus()) by {
                assert forall |au: AU|
                    #![trigger self.all_summary_aus().contains(au)]
                    self.all_summary_aus().contains(au)
                    == old(self).all_summary_aus().contains(au) by {
                    if self.all_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].summary.contains(au);
                        assert(old(self).records().contains_key(root));
                        assert(old(self).records()[root].summary.contains(au));
                    } else if old(self).all_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            old(self).records().contains_key(root)
                            && old(self).records()[root].summary.contains(au);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].summary.contains(au));
                    }
                }
            }
            assert(self.active_summary_map() == old(self).active_summary_map()) by {
                assert_maps_equal!(
                    self.active_summary_map(),
                    old(self).active_summary_map(),
                    root => { }
                );
            }
            assert(self.active_summary_aus()
                =~= initial_active_summary_aus) by {
                assert forall |au: AU|
                    #![trigger self.active_summary_aus().contains(au)]
                    self.active_summary_aus().contains(au)
                    == initial_active_summary_aus.contains(au) by {
                    if self.active_summary_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.active@.contains_key(root)
                            && self.active@[root].summary.contains(au);
                        assert(initial_active.contains_key(root));
                        assert(initial_active[root].summary.contains(au));
                    } else if initial_active_summary_aus.contains(au) {
                        let root = choose |root: AU| #![auto]
                            initial_active.contains_key(root)
                            && initial_active[root].summary.contains(au);
                        assert(self.active@.contains_key(root));
                        assert(self.active@[root].summary.contains(au));
                    }
                }
            }
            assert(self.persistent_aus() =~= initial_persistent) by {
                assert forall |au: AU|
                    #![trigger self.persistent_aus().contains(au)]
                    self.persistent_aus().contains(au)
                    == initial_persistent.contains(au) by {
                    if self.persistent_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].snapshots.persistent
                            && self.records()[root].summary.contains(au);
                        assert(initial_active.contains_key(root)
                            || initial_retired.contains_key(root));
                        assert((initial_active.union_prefer_right(initial_retired))
                            .contains_key(root));
                        assert((initial_active.union_prefer_right(initial_retired))[root]
                            .snapshots.persistent);
                        assert((initial_active.union_prefer_right(initial_retired))[root]
                            .summary.contains(au));
                        assert(exists |owner: AU| #![auto]
                            (initial_active.union_prefer_right(initial_retired))
                                .contains_key(owner)
                            && (initial_active.union_prefer_right(initial_retired))[owner]
                                .snapshots.persistent
                            && (initial_active.union_prefer_right(initial_retired))[owner]
                                .summary.contains(au));
                        assert(initial_persistent.contains(au));
                    } else if initial_persistent.contains(au) {
                        let root = choose |root: AU| #![auto]
                            (initial_active.union_prefer_right(initial_retired))
                                .contains_key(root)
                            && (initial_active.union_prefer_right(initial_retired))[root]
                                .snapshots.persistent
                            && (initial_active.union_prefer_right(initial_retired))[root]
                                .summary.contains(au);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].snapshots.persistent);
                        assert(self.records()[root].summary.contains(au));
                    }
                }
            }
            assert(self.frozen_aus()
                =~= initial_frozen + initial_active_summary_aus) by {
                assert forall |au: AU|
                    #![trigger self.frozen_aus().contains(au)]
                    self.frozen_aus().contains(au)
                    == (initial_frozen + initial_active_summary_aus)
                        .contains(au) by {
                    if initial_active_summary_aus.contains(au) {
                        let root = choose |root: AU| #![auto]
                            initial_active.contains_key(root)
                            && initial_active[root].summary.contains(au);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].snapshots.frozen);
                        assert(self.records()[root].summary.contains(au));
                    } else if initial_frozen.contains(au) {
                        let root = choose |root: AU| #![auto]
                            (initial_active.union_prefer_right(initial_retired))
                                .contains_key(root)
                            && (initial_active.union_prefer_right(initial_retired))[root]
                                .snapshots.frozen
                            && (initial_active.union_prefer_right(initial_retired))[root]
                                .summary.contains(au);
                        assert(self.records().contains_key(root));
                        assert(self.records()[root].snapshots.frozen);
                        assert(self.records()[root].summary.contains(au));
                    } else if self.frozen_aus().contains(au) {
                        let root = choose |root: AU| #![auto]
                            self.records().contains_key(root)
                            && self.records()[root].snapshots.frozen
                            && self.records()[root].summary.contains(au);
                        if initial_active.contains_key(root) {
                            assert(initial_active_summary_aus.contains(au));
                        } else {
                            assert(initial_retired[root].snapshots.frozen);
                            assert((initial_active.union_prefer_right(initial_retired))
                                .contains_key(root));
                            assert((initial_active.union_prefer_right(initial_retired))[root]
                                .snapshots.frozen);
                            assert((initial_active.union_prefer_right(initial_retired))[root]
                                .summary.contains(au));
                            assert(exists |owner: AU| #![auto]
                                (initial_active.union_prefer_right(initial_retired))
                                    .contains_key(owner)
                                && (initial_active.union_prefer_right(initial_retired))[owner]
                                    .snapshots.frozen
                                && (initial_active.union_prefer_right(initial_retired))[owner]
                                    .summary.contains(au));
                            assert(initial_frozen.contains(au));
                        }
                    }
                }
            }
            assert(initial_active == old(self).active@);
            assert(initial_retired == old(self).retired@);
            assert(initial_persistent =~= old(self).persistent_aus());
            assert(initial_frozen =~= old(self).frozen_aus());
            assert(initial_active_summary_aus
                =~= old(self).active_summary_aus());
        }
    }
}

impl View for BranchSummaryOwnershipImpl {
    type V = Map<AU, Summary>;

    open spec fn view(&self) -> Self::V {
        self.active_summary_map()
    }
}

impl BranchBetreeOwnershipImpl {
    pub open spec fn wf(&self) -> bool {
        &&& self.betree.wf()
        &&& self.branches.wf()
        &&& self.betree.active.bucket_count == self.branches.active.bucket_count
        &&& self.betree.all_aus().disjoint(self.branches.all_summary_aus())
    }

    pub open spec fn persistent_aus(&self) -> Set<AU> {
        self.betree.persistent_aus() + self.branches.persistent_aus()
    }

    pub open spec fn frozen_aus(&self) -> Set<AU> {
        self.betree.frozen_aus() + self.branches.frozen_aus()
    }

    pub open spec fn current_durable_aus(&self) -> Set<AU> {
        self.betree.active_aus() + self.branches.active_summary_aus()
    }

    pub proof fn current_durable_matches_views(
        &self,
        branch_likes: AULikes,
    )
        requires
            self.wf(),
            branch_likes.dom()
                == self.branches.active_summary_map().dom(),
        ensures
            self.current_durable_aus()
                =~= self.betree@.dom()
                    + branch_likes.dom()
                    + summary_aus(self.branches@),
    {
        self.betree.view_domain_matches_active();
        self.branches.active_summary_projection();
        self.branches.active_roots_are_summary_aus();
        assert(branch_likes.dom()
            <= self.branches.active_summary_aus());
        assert(self.current_durable_aus()
            =~= self.betree@.dom()
                + branch_likes.dom()
                + summary_aus(self.branches@)) by {
            assert forall |au: AU|
                #[trigger] self.current_durable_aus().contains(au)
                == (self.betree@.dom()
                    + branch_likes.dom()
                    + summary_aus(self.branches@)).contains(au) by {}
        }
    }

    pub proof fn fully_persistent_owns_only_persistent_aus(&self)
        requires
            self.wf(),
            self.betree.persistent_aus() =~= self.betree.active_aus(),
            self.branches.persistent_aus()
                =~= self.branches.active_summary_aus(),
            self.betree.frozen_aus().is_empty(),
            self.branches.frozen_aus().is_empty(),
        ensures
            self.betree.all_aus() =~= self.betree.persistent_aus(),
            self.branches.all_summary_aus()
                =~= self.branches.persistent_aus(),
            self.betree.all_aus() + self.branches.all_summary_aus()
                =~= self.persistent_aus(),
    {
        self.betree.ownership_sets_bounded();
        self.branches.ownership_sets_bounded();
        assert(self.betree.all_aus()
            =~= self.betree.persistent_aus()) by {
            assert forall |au: AU|
                #[trigger] self.betree.all_aus().contains(au)
                    == self.betree.persistent_aus().contains(au) by {
                if self.betree.all_aus().contains(au)
                    && !self.betree.active_aus().contains(au)
                {
                    assert(self.betree.retired@.contains_key(au));
                    assert(self.betree.retired@[au].protected());
                    if self.betree.retired@[au].frozen {
                        assert(self.betree.frozen_aus().contains(au));
                    } else {
                        assert(self.betree.retired@[au].persistent);
                        assert(self.betree.persistent_aus().contains(au));
                    }
                }
            }
        }
        assert(self.branches.all_summary_aus()
            =~= self.branches.persistent_aus()) by {
            assert forall |au: AU|
                #[trigger] self.branches.all_summary_aus().contains(au)
                    == self.branches.persistent_aus().contains(au) by {
                if self.branches.all_summary_aus().contains(au) {
                    let root = choose |root: AU| #![auto]
                        self.branches.records().contains_key(root)
                        && self.branches.records()[root].summary.contains(au);
                    if self.branches.active@.contains_key(root) {
                        assert(self.branches.active_summary_aus().contains(au));
                    } else {
                        assert(self.branches.retired@.contains_key(root));
                        assert(self.branches.retired@[root]
                            .snapshots.protected());
                        if self.branches.retired@[root].snapshots.frozen {
                            assert(self.branches.frozen_aus().contains(au));
                        } else {
                            assert(self.branches.retired@[root]
                                .snapshots.persistent);
                            assert(self.branches.persistent_aus().contains(au));
                        }
                    }
                }
            }
        }
    }

    pub fn new(bucket_count: u32) -> (out: Self)
        requires bucket_count > 0,
        ensures
            out.wf(),
            out.betree.active.bucket_count == bucket_count,
            out.betree.retired.bucket_count == bucket_count,
            out.branches.active.bucket_count == bucket_count,
            out.branches.retired.bucket_count == bucket_count,
            out.betree@ == AULikes::empty(),
            out.betree.all_aus() =~= Set::<AU>::empty(),
            out.branches.all_summary_aus() =~= Set::<AU>::empty(),
            out.branches.active@
                == Map::<AU, BranchSummaryRecordView>::empty(),
            out.branches.retired@
                == Map::<AU, BranchSummaryRecordView>::empty(),
            out.persistent_aus() =~= Set::<AU>::empty(),
            out.frozen_aus() =~= Set::<AU>::empty(),
            out.current_durable_aus() =~= Set::<AU>::empty(),
    {
        let betree = BetreeAuOwnershipImpl::new(bucket_count);
        let branches = BranchSummaryOwnershipImpl::new(bucket_count);
        let out = Self { betree, branches };
        proof {
            assert(out.wf());
            assert(out.betree.active_aus() =~= Set::<AU>::empty());
            out.branches.ownership_sets_bounded();
            assert(out.branches.active_summary_aus() =~= Set::<AU>::empty()) by {
                assert forall |au: AU|
                    #![trigger out.branches.active_summary_aus().contains(au)]
                    !out.branches.active_summary_aus().contains(au) by {
                    if out.branches.active_summary_aus().contains(au) {
                        assert(out.branches.all_summary_aus().contains(au));
                    }
                }
            }
            assert(out.current_durable_aus() =~= Set::<AU>::empty()) by {
                assert forall |au: AU|
                    #![trigger out.current_durable_aus().contains(au)]
                    !out.current_durable_aus().contains(au) by { }
            }
        }
        out
    }

    pub fn current_durable_aus_vec(&self) -> (out: Vec<IAU>)
        requires self.wf(),
        ensures
            unique_iau_seq(out@),
            iau_seq_set(out@) =~= self.current_durable_aus(),
    {
        let records = self.betree.active.flatten();
        let mut out = Vec::<IAU>::new();
        let mut index = 0usize;
        while index < records.len()
            invariant
                self.wf(),
                records@ == BetreeAuTable::flatten_prefix(
                    self.betree.active.buckets@,
                    self.betree.active.buckets@.len(),
                ),
                BetreeAuBucket::unique_aus(records@),
                BetreeAuBucket::entries_map(records@)
                    == self.betree.active@,
                index <= records.len(),
                out@ == records@.take(index as int).map(
                    |_index: int, record: BetreeAuRecord| record.au,
                ),
                unique_iau_seq(out@),
                iau_seq_set(out@)
                    =~= BetreeAuBucket::entries_map(
                        records@.take(index as int),
                    ).dom(),
            decreases records.len() - index,
        {
            let au = records[index].au;
            let ghost before = out@;
            proof {
                assert(!iau_seq_set(out@).contains(au as nat)) by {
                    if iau_seq_set(out@).contains(au as nat) {
                        let earlier = choose |earlier: int| #![auto]
                            0 <= earlier < out@.len()
                            && out@[earlier] == au;
                        assert(records@[earlier].au
                            == records@[index as int].au);
                        assert(earlier != index);
                    }
                }
            }
            out.push(au);
            proof {
                iau_seq_set_push(before, au);
                assert(records@.take(index as int + 1)
                    == records@.take(index as int)
                        .push(records@[index as int]));
                assert(!BetreeAuBucket::entries_map(
                    records@.take(index as int),
                ).contains_key(au as nat));
                BetreeAuBucket::entries_map_after_push(
                    records@.take(index as int),
                    records@[index as int],
                );
                assert(BetreeAuBucket::entries_map(
                    records@.take(index as int + 1),
                ).dom() =~= BetreeAuBucket::entries_map(
                    records@.take(index as int),
                ).dom().insert(au as nat)) by {
                    assert forall |candidate: AU|
                        #![trigger BetreeAuBucket::entries_map(
                            records@.take(index as int + 1),
                        ).dom().contains(candidate)]
                        BetreeAuBucket::entries_map(
                            records@.take(index as int + 1),
                        ).dom().contains(candidate)
                        == BetreeAuBucket::entries_map(
                            records@.take(index as int),
                        ).dom().insert(au as nat).contains(candidate) by { }
                }
            }
            index += 1;
        }
        proof {
            assert(records@.take(index as int) == records@);
            assert(iau_seq_set(out@) =~= self.betree.active_aus());
        }
        let branch_aus = self.branches.active_summary_aus_vec();
        proof {
            self.betree.ownership_sets_bounded();
            self.branches.ownership_sets_bounded();
            assert(iau_seq_set(out@).disjoint(iau_seq_set(branch_aus@))) by {
                assert(self.betree.active_aus()
                    <= self.betree.all_aus());
                assert(self.branches.active_summary_aus()
                    <= self.branches.all_summary_aus());
            }
        }
        append_unique_aus(&mut out, branch_aus);
        out
    }

    fn betree_records_bounded(
        records: &Vec<BetreeAuRecord>,
        total_aus: IAU,
    ) -> (out: bool)
        ensures
            out ==> forall |i: int| 0 <= i < records@.len() ==> {
                &&& 0 < #[trigger] (records@[i].au as nat)
                &&& (records@[i].au as nat) < total_aus as nat
            },
    {
        let mut index = 0usize;
        while index < records.len()
            invariant
                index <= records.len(),
                forall |i: int| 0 <= i < index ==> {
                    &&& 0 < #[trigger] (records@[i].au as nat)
                    &&& (records@[i].au as nat) < total_aus as nat
                },
            decreases records.len() - index,
        {
            let au = records[index].au;
            if au == 0 || au >= total_aus {
                return false;
            }
            index += 1;
        }
        true
    }

    fn iau_values_bounded(
        aus: &Vec<IAU>,
        total_aus: IAU,
    ) -> (out: bool)
        ensures
            out ==> forall |i: int| 0 <= i < aus@.len() ==> {
                &&& 0 < #[trigger] (aus@[i] as nat)
                &&& (aus@[i] as nat) < total_aus as nat
            },
    {
        let mut index = 0usize;
        while index < aus.len()
            invariant
                index <= aus.len(),
                forall |i: int| 0 <= i < index ==> {
                    &&& 0 < #[trigger] (aus@[i] as nat)
                    &&& (aus@[i] as nat) < total_aus as nat
                },
            decreases aus.len() - index,
        {
            let au = aus[index];
            if au == 0 || au >= total_aus {
                return false;
            }
            index += 1;
        }
        true
    }

    pub fn all_owned_aus_bounded(
        &self,
        total_aus: IAU,
    ) -> (out: bool)
        requires self.wf(),
        ensures
            out ==> forall |au: AU| #[trigger]
                (self.betree.all_aus()
                    + self.branches.all_summary_aus()).contains(au)
                ==> 0 < au && au < total_aus as nat,
    {
        let betree_active = self.betree.active.flatten();
        if !Self::betree_records_bounded(&betree_active, total_aus) {
            return false;
        }
        let betree_retired = self.betree.retired.flatten();
        if !Self::betree_records_bounded(&betree_retired, total_aus) {
            return false;
        }
        proof {
            assert(self.branches.active.summaries_pairwise_disjoint()) by {
                assert forall |left: AU, right: AU|
                    #![trigger self.branches.active@.contains_key(left),
                        self.branches.active@.contains_key(right)]
                    self.branches.active@.contains_key(left)
                        && self.branches.active@.contains_key(right)
                        && left != right
                    implies self.branches.active@[left].summary.disjoint(
                        self.branches.active@[right].summary,
                    ) by {
                    assert(self.branches.records()[left]
                        == self.branches.active@[left]);
                    assert(self.branches.records()[right]
                        == self.branches.active@[right]);
                }
            }
            assert(self.branches.retired.summaries_pairwise_disjoint()) by {
                assert forall |left: AU, right: AU|
                    #![trigger self.branches.retired@.contains_key(left),
                        self.branches.retired@.contains_key(right)]
                    self.branches.retired@.contains_key(left)
                        && self.branches.retired@.contains_key(right)
                        && left != right
                    implies self.branches.retired@[left].summary.disjoint(
                        self.branches.retired@[right].summary,
                    ) by {
                    assert(self.branches.summaries_pairwise_disjoint());
                    assert(self.branches.records().contains_key(left));
                    assert(self.branches.records().contains_key(right));
                    assert(self.branches.records()[left]
                        == self.branches.retired@[left]);
                    assert(self.branches.records()[right]
                        == self.branches.retired@[right]);
                }
            }
        }
        let branch_active = self.branches.active.flatten_summary_aus();
        if !Self::iau_values_bounded(&branch_active, total_aus) {
            return false;
        }
        let branch_retired = self.branches.retired.flatten_summary_aus();
        if !Self::iau_values_bounded(&branch_retired, total_aus) {
            return false;
        }
        proof {
            assert forall |au: AU| #[trigger]
                (self.betree.all_aus()
                    + self.branches.all_summary_aus()).contains(au)
                implies 0 < au && au < total_aus as nat by {
                if self.betree.all_aus().contains(au) {
                    if self.betree.active@.contains_key(au) {
                        let i = choose |i: int| #![auto]
                            0 <= i < betree_active@.len()
                            && betree_active@[i].au as nat == au;
                    } else {
                        let i = choose |i: int| #![auto]
                            0 <= i < betree_retired@.len()
                            && betree_retired@[i].au as nat == au;
                    }
                } else {
                    if self.branches.active.summary_aus().contains(au) {
                        let i = choose |i: int| #![auto]
                            0 <= i < branch_active@.len()
                            && branch_active@[i] as nat == au;
                    } else {
                        assert(self.branches.retired.summary_aus().contains(au));
                        let i = choose |i: int| #![auto]
                            0 <= i < branch_retired@.len()
                            && branch_retired@[i] as nat == au;
                    }
                }
            }
        }
        true
    }

    pub fn allocate_betree_au(
        &mut self,
        au: IAU,
    ) -> (result: BetreeOwnershipUpdateResult)
        requires
            old(self).wf(),
            old(self).branches.all_summary_aus().disjoint(set![au as nat]),
        ensures
            self.wf(),
            (result is Applied) <==>
                !old(self).betree.all_aus().contains(au as nat),
            self.branches@ == old(self).branches@,
            self.betree.active.bucket_count
                == old(self).betree.active.bucket_count,
            self.betree.retired.bucket_count
                == old(self).betree.retired.bucket_count,
            self.branches.all_summary_aus()
                == old(self).branches.all_summary_aus(),
            match result {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.betree.active@
                        == old(self).betree.active@.insert(
                            au as nat,
                            SnapshotMembership {
                                persistent: false,
                                frozen: false,
                            },
                        )
                    &&& self.betree.retired@
                        == old(self).betree.retired@
                    &&& self.betree@ == old(self).betree@.insert(au as nat)
                    &&& self.betree.active_aus()
                        =~= old(self).betree.active_aus().insert(au as nat)
                    &&& self.betree.all_aus()
                        =~= old(self).betree.all_aus().insert(au as nat)
                    &&& self.betree.persistent_aus()
                        =~= old(self).betree.persistent_aus()
                    &&& self.betree.frozen_aus()
                        =~= old(self).betree.frozen_aus()
                    &&& self.persistent_aus()
                        =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BetreeOwnershipUpdateResult::Noop => {
                    &&& self.betree.active.buckets@
                        == old(self).betree.active.buckets@
                    &&& self.betree.retired.buckets@
                        == old(self).betree.retired.buckets@
                    &&& self.betree@ == old(self).betree@
                },
            },
    {
        let result = self.betree.allocate(au);
        proof {
            assert(self.betree.all_aus().disjoint(
                self.branches.all_summary_aus(),
            )) by {
                assert forall |candidate: AU|
                    #[trigger] self.betree.all_aus().contains(candidate)
                    implies !self.branches.all_summary_aus().contains(candidate) by {
                    if candidate == au as nat {
                        assert(!old(self).branches.all_summary_aus()
                            .contains(candidate));
                    } else {
                        assert(self.betree.all_aus().contains(candidate)
                            == old(self).betree.all_aus().contains(candidate));
                    }
                }
            }
            assert(self.wf());
        }
        result
    }

    pub fn add_ephemeral_branch(
        &mut self,
        root_au: IAU,
        summary: Vec<IAU>,
    ) -> (result: BranchOwnershipUpdateResult)
        requires
            old(self).wf(),
            unique_iau_seq(summary@),
            iau_seq_set(summary@).contains(root_au as nat),
            old(self).branches.all_summary_aus().disjoint(
                iau_seq_set(summary@),
            ),
            old(self).betree.all_aus().disjoint(iau_seq_set(summary@)),
        ensures
            self.wf(),
            result is Applied,
            (result is Applied) <==>
                !old(self).branches.active@.contains_key(root_au as nat)
                    && !old(self).branches.retired@.contains_key(
                        root_au as nat,
                    ),
            self.betree == old(self).betree,
            self.betree@ == old(self).betree@,
            self.betree.all_aus() == old(self).betree.all_aus(),
            self.branches.active.bucket_count
                == old(self).branches.active.bucket_count,
            self.branches.retired.bucket_count
                == old(self).branches.retired.bucket_count,
            match result {
                BranchOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& reclaimed@.len() == 0
                    &&& self.branches.active_summary_map()
                        == old(self).branches.active_summary_map().insert(
                            root_au as nat,
                            iau_seq_set(summary@),
                        )
                    &&& self.branches.active_summary_aus()
                        =~= old(self).branches.active_summary_aus()
                            + iau_seq_set(summary@)
                    &&& self.branches.all_summary_aus()
                        =~= old(self).branches.all_summary_aus()
                            + iau_seq_set(summary@)
                    &&& self.branches.persistent_aus()
                        =~= old(self).branches.persistent_aus()
                    &&& self.branches.frozen_aus()
                        =~= old(self).branches.frozen_aus()
                    &&& self.persistent_aus()
                        =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                },
                BranchOwnershipUpdateResult::Noop => {
                    &&& self.branches.active.buckets@
                        == old(self).branches.active.buckets@
                    &&& self.branches.retired.buckets@
                        == old(self).branches.retired.buckets@
                    &&& self.branches@ == old(self).branches@
                },
            },
    {
        let ghost added = iau_seq_set(summary@);
        proof {
            assert(!old(self).branches.active@.contains_key(root_au as nat)) by {
                if old(self).branches.active@.contains_key(root_au as nat) {
                    old(self).branches.root_record_is_owned(root_au as nat);
                    assert(added.contains(root_au as nat));
                }
            }
            assert(!old(self).branches.retired@.contains_key(root_au as nat)) by {
                if old(self).branches.retired@.contains_key(root_au as nat) {
                    old(self).branches.root_record_is_owned(root_au as nat);
                    assert(added.contains(root_au as nat));
                }
            }
        }
        let result = self.branches.add_ephemeral(root_au, summary);
        proof {
            assert(self.betree.all_aus().disjoint(
                self.branches.all_summary_aus(),
            )) by {
                assert forall |au: AU|
                    #[trigger] self.betree.all_aus().contains(au)
                    implies !self.branches.all_summary_aus().contains(au) by {
                    if self.branches.all_summary_aus().contains(au)
                        && !old(self).branches.all_summary_aus().contains(au)
                    {
                        assert(added.contains(au));
                    }
                }
            }
            assert(self.wf());
        }
        result
    }

    pub fn replace_betree_au(
        &mut self,
        old_au: IAU,
        new_au: IAU,
    ) -> (result: BetreeOwnershipUpdateResult)
        requires
            old(self).wf(),
            old(self).betree.active_aus().contains(old_au as nat),
            !old(self).betree.all_aus().contains(new_au as nat),
            old(self).branches.all_summary_aus().disjoint(
                set![new_au as nat],
            ),
            old_au != new_au,
        ensures
            self.wf(),
            result is Applied,
            self.betree@ == old(self).betree@.remove(
                old_au as nat,
            ).insert(new_au as nat),
            self.betree.active_aus()
                =~= old(self).betree.active_aus()
                    .remove(old_au as nat)
                    .insert(new_au as nat),
            self.betree.all_aus()
                <= old(self).betree.all_aus().insert(new_au as nat),
            self.betree.active.bucket_count
                == old(self).betree.active.bucket_count,
            self.betree.retired.bucket_count
                == old(self).betree.retired.bucket_count,
            self.branches@ == old(self).branches@,
            self.branches.all_summary_aus()
                == old(self).branches.all_summary_aus(),
            self.persistent_aus() =~= old(self).persistent_aus(),
            self.frozen_aus() =~= old(self).frozen_aus(),
            match result {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@)
                        =~= if old(self).betree.active@[old_au as nat]
                            .unprotected()
                        {
                            set![old_au as nat]
                        } else {
                            Set::<AU>::empty()
                        }
                },
                BetreeOwnershipUpdateResult::Noop => false,
            },
    {
        let ghost initial_betree = self.betree@;
        let ghost initial_active = self.betree.active_aus();
        let ghost old_snapshots = self.betree.active@[old_au as nat];
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();
        let allocated = self.allocate_betree_au(new_au);
        match allocated {
            BetreeOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BetreeOwnershipUpdateResult::Noop;
            },
        }
        proof {
            assert(self.betree.active@[old_au as nat] == old_snapshots);
        }
        let retired = self.betree.retire(old_au);
        proof {
            assert(retired is Applied);
            assert(self.betree.active_aus()
                =~= initial_active.remove(old_au as nat)
                    .insert(new_au as nat));
            assert(self.betree.all_aus().disjoint(
                self.branches.all_summary_aus(),
            )) by {
                assert(self.betree.all_aus()
                    <= old(self).betree.all_aus().insert(new_au as nat));
            }
            assert(self.wf());
            assert(self.persistent_aus() =~= initial_persistent);
            assert(self.frozen_aus() =~= initial_frozen);
            assert(old_snapshots
                == old(self).betree.active@[old_au as nat]);
            broadcast use vstd::multiset::group_multiset_axioms;
            assert_multisets_equal!(
                self.betree@,
                initial_betree.remove(old_au as nat).insert(new_au as nat),
                au => {
                    self.betree.view_count_matches_active(au);
                    old(self).betree.view_count_matches_active(au);
                    if au == old_au as nat {
                        assert(!self.betree.active_aus().contains(au));
                        assert(old(self).betree.active_aus().contains(au));
                    } else if au == new_au as nat {
                        assert(self.betree.active_aus().contains(au));
                        assert(!old(self).betree.active_aus().contains(au));
                    } else {
                        assert(self.betree.active_aus().contains(au)
                            == old(self).betree.active_aus().contains(au));
                    }
                }
            );
        }
        retired
    }

    pub fn replace_betree_aus(
        &mut self,
        old_aus: &Vec<IAU>,
        new_aus: &Vec<IAU>,
    ) -> (result: BetreeOwnershipUpdateResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            (result is Applied) <==> betree_batch_replace_applicable(
                *old(self),
                old_aus@,
                new_aus@,
            ),
            self.betree.active.bucket_count
                == old(self).betree.active.bucket_count,
            self.betree.retired.bucket_count
                == old(self).betree.retired.bucket_count,
            self.branches.active.bucket_count
                == old(self).branches.active.bucket_count,
            self.branches.retired.bucket_count
                == old(self).branches.retired.bucket_count,
            match result {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => {
                    &&& self.betree@ == old(self).betree@
                        .sub(seq_to_au_likes(old_aus@))
                        .add(seq_to_au_likes(new_aus@))
                    &&& self.betree.active_aus()
                        =~= (old(self).betree.active_aus()
                            - iau_seq_set(old_aus@))
                            + iau_seq_set(new_aus@)
                    &&& old(self).betree@.dom() - self.betree@.dom()
                        =~= iau_seq_set(old_aus@)
                    &&& self.betree.all_aus()
                        <= old(self).betree.all_aus()
                            + iau_seq_set(new_aus@)
                    &&& self.branches@ == old(self).branches@
                    &&& self.branches.all_summary_aus()
                        == old(self).branches.all_summary_aus()
                    &&& self.persistent_aus()
                        =~= old(self).persistent_aus()
                    &&& self.frozen_aus() =~= old(self).frozen_aus()
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@)
                        =~= iau_seq_set(old_aus@)
                            - old(self).betree.persistent_aus()
                            - old(self).betree.frozen_aus()
                    &&& iau_seq_set(reclaimed@)
                        <= old(self).betree@.dom() - self.betree@.dom()
                },
                BetreeOwnershipUpdateResult::Noop => {
                    &&& self.betree.active.buckets@
                        == old(self).betree.active.buckets@
                    &&& self.betree.retired.buckets@
                        == old(self).betree.retired.buckets@
                    &&& self.branches.active.buckets@
                        == old(self).branches.active.buckets@
                    &&& self.branches.retired.buckets@
                        == old(self).branches.retired.buckets@
                    &&& self.betree@ == old(self).betree@
                    &&& self.branches@ == old(self).branches@
                },
            },
    {
        let ghost initial_betree = self.betree@;
        let ghost initial_active = self.betree.active_aus();
        let ghost initial_all = self.betree.all_aus();
        let ghost initial_persistent = self.persistent_aus();
        let ghost initial_frozen = self.frozen_aus();
        let ghost initial_betree_persistent = self.betree.persistent_aus();
        let ghost initial_betree_frozen = self.betree.frozen_aus();
        let ghost initial_branches = self.branches@;
        let ghost initial_branch_aus = self.branches.all_summary_aus();
        let active_bucket_count = self.betree.active.bucket_count;
        let retired_bucket_count = self.betree.retired.bucket_count;
        let branch_active_bucket_count = self.branches.active.bucket_count;
        let branch_retired_bucket_count = self.branches.retired.bucket_count;
        proof {
            self.betree.view_domain_matches_active();
            self.betree.ownership_sets_bounded();
        }

        if !iau_vec_unique(old_aus) || !iau_vec_unique(new_aus) {
            return BetreeOwnershipUpdateResult::Noop;
        }

        let mut check_old = 0usize;
        while check_old < old_aus.len()
            invariant
                self.wf(),
                self.betree@ == initial_betree,
                self.betree.active_aus() == initial_active,
                self.betree.all_aus() == initial_all,
                self.persistent_aus() == initial_persistent,
                self.frozen_aus() == initial_frozen,
                self.betree.persistent_aus() == initial_betree_persistent,
                self.betree.frozen_aus() == initial_betree_frozen,
                self.branches@ == initial_branches,
                self.branches.all_summary_aus() == initial_branch_aus,
                self.betree.active.bucket_count == active_bucket_count,
                self.betree.retired.bucket_count == retired_bucket_count,
                self.branches.active.bucket_count == branch_active_bucket_count,
                self.branches.retired.bucket_count == branch_retired_bucket_count,
                check_old <= old_aus.len(),
                forall |i: int| #![trigger old_aus@[i]]
                    0 <= i < check_old
                    ==> initial_active.contains(old_aus@[i] as nat),
            decreases old_aus.len() - check_old,
        {
            if !self.betree.contains_active(old_aus[check_old]) {
                return BetreeOwnershipUpdateResult::Noop;
            }
            check_old += 1;
        }

        let mut check_new = 0usize;
        while check_new < new_aus.len()
            invariant
                self.wf(),
                self.betree@ == initial_betree,
                self.betree.active_aus() == initial_active,
                self.betree.all_aus() == initial_all,
                self.persistent_aus() == initial_persistent,
                self.frozen_aus() == initial_frozen,
                self.betree.persistent_aus() == initial_betree_persistent,
                self.betree.frozen_aus() == initial_betree_frozen,
                self.branches@ == initial_branches,
                self.branches.all_summary_aus() == initial_branch_aus,
                self.betree.active.bucket_count == active_bucket_count,
                self.betree.retired.bucket_count == retired_bucket_count,
                self.branches.active.bucket_count == branch_active_bucket_count,
                self.branches.retired.bucket_count == branch_retired_bucket_count,
                check_new <= new_aus.len(),
                forall |i: int| #![trigger new_aus@[i]]
                    0 <= i < check_new
                    ==> !initial_all.contains(new_aus@[i] as nat)
                        && !initial_branch_aus.contains(new_aus@[i] as nat),
            decreases new_aus.len() - check_new,
        {
            if self.betree.contains_owned_au(new_aus[check_new])
                || self.branches.contains_owned_au(new_aus[check_new])
            {
                return BetreeOwnershipUpdateResult::Noop;
            }
            check_new += 1;
        }

        proof {
            assert(iau_seq_set(old_aus@) <= initial_active) by {
                assert forall |au: AU|
                    #[trigger] iau_seq_set(old_aus@).contains(au)
                    implies initial_active.contains(au) by {
                    let i = choose |i: int| #![auto]
                        0 <= i < old_aus@.len()
                        && old_aus@[i] as nat == au;
                }
            }
            assert(initial_all.disjoint(iau_seq_set(new_aus@))) by {
                assert forall |au: AU| #[trigger] initial_all.contains(au)
                    implies !iau_seq_set(new_aus@).contains(au) by {
                    if iau_seq_set(new_aus@).contains(au) {
                        let i = choose |i: int| #![auto]
                            0 <= i < new_aus@.len()
                            && new_aus@[i] as nat == au;
                    }
                }
            }
            assert(initial_branch_aus.disjoint(iau_seq_set(new_aus@))) by {
                assert forall |au: AU| #[trigger] initial_branch_aus.contains(au)
                    implies !iau_seq_set(new_aus@).contains(au) by {
                    if iau_seq_set(new_aus@).contains(au) {
                        let i = choose |i: int| #![auto]
                            0 <= i < new_aus@.len()
                            && new_aus@[i] as nat == au;
                    }
                }
            }
        }

        let mut add_index = 0usize;
        while add_index < new_aus.len()
            invariant
                self.wf(),
                unique_iau_seq(new_aus@),
                add_index <= new_aus.len(),
                self.betree.active_aus()
                    =~= initial_active
                        + iau_seq_set(new_aus@.take(add_index as int)),
                self.betree.all_aus()
                    =~= initial_all
                        + iau_seq_set(new_aus@.take(add_index as int)),
                self.persistent_aus() =~= initial_persistent,
                self.frozen_aus() =~= initial_frozen,
                self.betree.persistent_aus() =~= initial_betree_persistent,
                self.betree.frozen_aus() =~= initial_betree_frozen,
                self.branches@ == initial_branches,
                self.branches.all_summary_aus() == initial_branch_aus,
                self.betree.active.bucket_count == active_bucket_count,
                self.betree.retired.bucket_count == retired_bucket_count,
                self.branches.active.bucket_count == branch_active_bucket_count,
                self.branches.retired.bucket_count == branch_retired_bucket_count,
            decreases new_aus.len() - add_index,
        {
            let au = new_aus[add_index];
            proof {
                assert(!self.betree.all_aus().contains(au as nat)) by {
                    if iau_seq_set(new_aus@.take(add_index as int))
                        .contains(au as nat)
                    {
                        let earlier = choose |i: int| #![auto]
                            0 <= i < add_index
                            && new_aus@[i] == au;
                        assert(earlier != add_index);
                    }
                }
                assert(self.branches.all_summary_aus().disjoint(
                    set![au as nat],
                ));
            }
            let allocated = self.allocate_betree_au(au);
            proof {
                assert(allocated is Applied);
                assert(new_aus@.take(add_index as int + 1)
                    == new_aus@.take(add_index as int).push(au));
                iau_seq_set_push(new_aus@.take(add_index as int), au);
            }
            add_index += 1;
        }

        let ghost all_new = iau_seq_set(new_aus@);
        proof {
            assert(new_aus@.take(add_index as int) == new_aus@);
            assert(self.betree.active_aus() =~= initial_active + all_new);
            assert(self.betree.active_aus()
                =~= (initial_active - iau_seq_set(Seq::<IAU>::empty()))
                    + all_new) by {
                assert(iau_seq_set(Seq::<IAU>::empty())
                    =~= Set::<AU>::empty()) by {
                    assert forall |au: AU|
                        #[trigger] iau_seq_set(Seq::<IAU>::empty()).contains(au)
                        implies false by {}
                }
                assert forall |au: AU|
                    #![trigger self.betree.active_aus().contains(au)]
                    self.betree.active_aus().contains(au)
                    == ((initial_active
                            - iau_seq_set(Seq::<IAU>::empty()))
                        + all_new).contains(au) by {}
            }
        }
        let mut reclaimed = Vec::<IAU>::new();
        let mut retire_index = 0usize;
        while retire_index < old_aus.len()
            invariant
                self.wf(),
                unique_iau_seq(old_aus@),
                retire_index <= old_aus.len(),
                self.betree.active_aus()
                    =~= (initial_active
                            - iau_seq_set(old_aus@.take(retire_index as int)))
                        + all_new,
                self.betree.all_aus()
                    <= initial_all + all_new,
                self.persistent_aus() =~= initial_persistent,
                self.frozen_aus() =~= initial_frozen,
                self.betree.persistent_aus() =~= initial_betree_persistent,
                self.betree.frozen_aus() =~= initial_betree_frozen,
                self.branches@ == initial_branches,
                self.branches.all_summary_aus() == initial_branch_aus,
                self.betree.active.bucket_count == active_bucket_count,
                self.betree.retired.bucket_count == retired_bucket_count,
                self.branches.active.bucket_count == branch_active_bucket_count,
                self.branches.retired.bucket_count == branch_retired_bucket_count,
                unique_iau_seq(reclaimed@),
                iau_seq_set(reclaimed@)
                    =~= iau_seq_set(old_aus@.take(retire_index as int))
                        - initial_betree_persistent
                        - initial_betree_frozen,
            decreases old_aus.len() - retire_index,
        {
            let au = old_aus[retire_index];
            proof {
                assert(self.betree.active_aus().contains(au as nat)) by {
                    assert(initial_active.contains(au as nat));
                    assert(!iau_seq_set(old_aus@.take(retire_index as int))
                        .contains(au as nat)) by {
                        if iau_seq_set(old_aus@.take(retire_index as int))
                            .contains(au as nat)
                        {
                            let earlier = choose |i: int| #![auto]
                                0 <= i < retire_index
                                && old_aus@[i] == au;
                            assert(earlier != retire_index);
                        }
                    }
                }
            }
            let ghost before_reclaimed = reclaimed@;
            let ghost before_reclaimed_set = iau_seq_set(reclaimed@);
            let ghost before_snapshots = self.betree.active@[au as nat];
            let retired = self.betree.retire(au);
            let newly_reclaimed = match retired {
                BetreeOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
                BetreeOwnershipUpdateResult::Noop => {
                    proof { assert(false); }
                    return BetreeOwnershipUpdateResult::Noop;
                },
            };
            proof {
                assert(unique_iau_seq(newly_reclaimed@));
                assert(before_snapshots.persistent
                    == initial_betree_persistent.contains(au as nat)) by {
                    assert(self.betree.persistent_aus()
                        =~= initial_betree_persistent);
                }
                assert(before_snapshots.frozen
                    == initial_betree_frozen.contains(au as nat)) by {
                    assert(self.betree.frozen_aus()
                        =~= initial_betree_frozen);
                }
                assert(iau_seq_set(newly_reclaimed@)
                    =~= if !initial_betree_persistent.contains(au as nat)
                        && !initial_betree_frozen.contains(au as nat)
                    {
                        set![au as nat]
                    } else {
                        Set::<AU>::empty()
                    });
                assert(iau_seq_set(reclaimed@).disjoint(
                    iau_seq_set(newly_reclaimed@),
                )) by {
                    assert forall |candidate: AU|
                        #[trigger] iau_seq_set(reclaimed@).contains(candidate)
                        implies !iau_seq_set(newly_reclaimed@).contains(candidate) by {
                        if iau_seq_set(newly_reclaimed@).contains(candidate) {
                            assert(candidate == au as nat);
                            assert(!iau_seq_set(old_aus@
                                .take(retire_index as int)).contains(candidate));
                        }
                    }
                }
            }
            append_unique_aus(&mut reclaimed, newly_reclaimed);
            proof {
                assert(old_aus@.take(retire_index as int + 1)
                    == old_aus@.take(retire_index as int).push(au));
                iau_seq_set_push(old_aus@.take(retire_index as int), au);
                assert(iau_seq_set(reclaimed@)
                    =~= iau_seq_set(old_aus@
                            .take(retire_index as int + 1))
                        - initial_betree_persistent
                        - initial_betree_frozen) by {
                    assert(iau_seq_set(reclaimed@)
                        =~= before_reclaimed_set
                            + iau_seq_set(newly_reclaimed@));
                }
                assert(self.wf()) by {
                    assert(self.betree.all_aus().disjoint(
                        self.branches.all_summary_aus(),
                    ));
                }
            }
            retire_index += 1;
        }

        proof {
            assert(old_aus@.take(retire_index as int) == old_aus@);
            assert(new_aus@.take(add_index as int) == new_aus@);
            assert(self.betree.active_aus()
                =~= (initial_active - iau_seq_set(old_aus@))
                    + iau_seq_set(new_aus@));
            broadcast use vstd::multiset::group_multiset_axioms;
            assert_multisets_equal!(
                self.betree@,
                initial_betree.sub(seq_to_au_likes(old_aus@))
                    .add(seq_to_au_likes(new_aus@)),
                au => {
                    self.betree.view_count_matches_active(au);
                    old(self).betree.view_count_matches_active(au);
                    unique_iau_seq_likes_count(old_aus@, au);
                    unique_iau_seq_likes_count(new_aus@, au);
                }
            );
            assert(self.wf());
            assert(self.betree.active.bucket_count == active_bucket_count);
            assert(self.betree.retired.bucket_count == retired_bucket_count);
            assert(self.branches.active.bucket_count
                == branch_active_bucket_count);
            assert(self.branches.retired.bucket_count
                == branch_retired_bucket_count);
            self.betree.view_domain_matches_active();
            old(self).betree.view_domain_matches_active();
            assert_sets_equal!(
                initial_betree.dom() - self.betree@.dom(),
                iau_seq_set(old_aus@),
                au => {
                    if iau_seq_set(old_aus@).contains(au) {
                        assert(initial_active.contains(au));
                        assert(!iau_seq_set(new_aus@).contains(au)) by {
                            assert(initial_all.contains(au));
                            assert(initial_all.disjoint(
                                iau_seq_set(new_aus@),
                            ));
                        }
                        assert(!self.betree.active_aus().contains(au));
                    } else if initial_betree.dom().contains(au)
                        && !self.betree@.dom().contains(au)
                    {
                        assert(initial_active.contains(au));
                        assert(!((initial_active - iau_seq_set(old_aus@))
                            + iau_seq_set(new_aus@)).contains(au));
                        assert(iau_seq_set(old_aus@).contains(au));
                    }
                }
            );
            assert(iau_seq_set(reclaimed@)
                <= initial_active - self.betree.active_aus()) by {
                assert forall |au: AU|
                    #[trigger] iau_seq_set(reclaimed@).contains(au)
                    implies initial_active.contains(au)
                        && !self.betree.active_aus().contains(au) by {
                    assert(iau_seq_set(old_aus@).contains(au));
                    assert(initial_active.contains(au));
                    if self.betree.active_aus().contains(au) {
                        assert(iau_seq_set(new_aus@).contains(au));
                        assert(initial_all.contains(au));
                        assert(initial_all.disjoint(
                            iau_seq_set(new_aus@),
                        ));
                    }
                }
            }
            assert(iau_seq_set(reclaimed@)
                <= initial_betree.dom() - self.betree@.dom());
        }
        BetreeOwnershipUpdateResult::Applied { reclaimed }
    }

    pub fn freeze_current(&mut self)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.betree.active.bucket_count
                == old(self).betree.active.bucket_count,
            self.branches.active.bucket_count
                == old(self).branches.active.bucket_count,
            self.betree.active_aus() =~= old(self).betree.active_aus(),
            self.branches.active_summary_map()
                == old(self).branches.active_summary_map(),
            self.branches.active_summary_aus()
                =~= old(self).branches.active_summary_aus(),
            self.betree.all_aus() =~= old(self).betree.all_aus(),
            self.branches.all_summary_aus()
                =~= old(self).branches.all_summary_aus(),
            self.current_durable_aus() =~= old(self).current_durable_aus(),
            self.persistent_aus() =~= old(self).persistent_aus(),
            self.frozen_aus()
                =~= old(self).frozen_aus() + old(self).current_durable_aus(),
    {
        self.betree.freeze_current();
        self.branches.freeze_current();
        proof {
            assert(self.betree.all_aus() == old(self).betree.all_aus());
            assert(self.branches.all_summary_aus()
                == old(self).branches.all_summary_aus()) by {
                assert forall |au: AU|
                    #![trigger self.branches.all_summary_aus().contains(au)]
                    self.branches.all_summary_aus().contains(au)
                    == old(self).branches.all_summary_aus().contains(au) by { }
            }
            assert(self.wf());
        }
    }

    pub fn commit_complete(&mut self) -> (reclaimed: Vec<IAU>)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.betree.active.bucket_count
                == old(self).betree.active.bucket_count,
            self.branches.active.bucket_count
                == old(self).branches.active.bucket_count,
            self.betree.active_aus() =~= old(self).betree.active_aus(),
            self.branches.active_summary_map()
                == old(self).branches.active_summary_map(),
            self.branches.active_summary_aus()
                =~= old(self).branches.active_summary_aus(),
            self.betree.all_aus() <= old(self).betree.all_aus(),
            self.branches.all_summary_aus()
                <= old(self).branches.all_summary_aus(),
            self.current_durable_aus() =~= old(self).current_durable_aus(),
            self.persistent_aus() =~= old(self).frozen_aus(),
            self.frozen_aus() =~= Set::<AU>::empty(),
            unique_iau_seq(reclaimed@),
            iau_seq_set(reclaimed@)
                =~= old(self).persistent_aus()
                    - old(self).frozen_aus()
                    - old(self).current_durable_aus(),
    {
        let ghost initial_betree_all = self.betree.all_aus();
        let ghost initial_betree_persistent = self.betree.persistent_aus();
        let ghost initial_betree_frozen = self.betree.frozen_aus();
        let ghost initial_betree_current = self.betree.active_aus();
        let ghost initial_branch_all = self.branches.all_summary_aus();
        let ghost initial_branch_persistent = self.branches.persistent_aus();
        let ghost initial_branch_frozen = self.branches.frozen_aus();
        let ghost initial_branch_current = self.branches.active_summary_aus();
        let ghost component_reclaimed =
            (initial_betree_persistent
                - initial_betree_frozen
                - initial_betree_current)
            + (initial_branch_persistent
                - initial_branch_frozen
                - initial_branch_current);
        let ghost combined_reclaimed =
            self.persistent_aus() - self.frozen_aus() - self.current_durable_aus();
        proof {
            self.betree.ownership_sets_bounded();
            self.branches.ownership_sets_bounded();
            disjoint_component_reclaims(
                initial_betree_all,
                initial_betree_persistent,
                initial_betree_frozen,
                initial_betree_current,
                initial_branch_all,
                initial_branch_persistent,
                initial_branch_frozen,
                initial_branch_current,
            );
            assert(component_reclaimed =~= combined_reclaimed);
        }
        let mut betree_reclaimed = self.betree.commit_complete();
        let branch_reclaimed = self.branches.commit_complete();
        proof {
            assert(iau_seq_set(betree_reclaimed@)
                .disjoint(iau_seq_set(branch_reclaimed@))) by {
                assert(iau_seq_set(betree_reclaimed@)
                    <= old(self).betree.all_aus());
                assert(iau_seq_set(branch_reclaimed@)
                    <= old(self).branches.all_summary_aus());
            }
        }
        append_unique_aus(&mut betree_reclaimed, branch_reclaimed);
        let reclaimed = betree_reclaimed;
        proof {
            assert(self.betree.all_aus() <= old(self).betree.all_aus());
            assert(self.branches.all_summary_aus()
                <= old(self).branches.all_summary_aus()) by {
                assert forall |au: AU|
                    #![trigger self.branches.all_summary_aus().contains(au)]
                    self.branches.all_summary_aus().contains(au)
                    implies old(self).branches.all_summary_aus().contains(au) by { }
            }
            assert(self.wf());
            assert(self.persistent_aus() =~= old(self).frozen_aus());
            assert(self.frozen_aus() =~= Set::<AU>::empty());
            assert(iau_seq_set(reclaimed@) =~= component_reclaimed);
            assert(combined_reclaimed
                =~= old(self).persistent_aus()
                    - old(self).frozen_aus()
                    - old(self).current_durable_aus());
            assert(iau_seq_set(reclaimed@)
                =~= old(self).persistent_aus()
                    - old(self).frozen_aus()
                    - old(self).current_durable_aus());
        }
        reclaimed
    }
}

#[allow(dead_code)]
fn verify_betree_ownership_cases() {
    let mut ownership = BetreeAuOwnershipImpl::new(2);
    let first = ownership.allocate(1);
    let collision = ownership.allocate(3);
    proof {
        assert(first is Applied);
        assert(collision is Applied);
        assert(ownership.active_aus() =~= set![1nat, 3nat]);
    }
    let duplicate = ownership.allocate(1);
    proof { assert(duplicate is Noop); }
    let retired = ownership.retire(1);
    match retired {
        BetreeOwnershipUpdateResult::Applied { reclaimed } => {
            proof {
                assert(iau_seq_set(reclaimed@) =~= set![1nat]);
                assert(ownership.active_aus() =~= set![3nat]);
            }
        },
        BetreeOwnershipUpdateResult::Noop => { proof { assert(false); } },
    }
}

#[allow(dead_code)]
fn verify_betree_snapshot_lifecycle() {
    let mut ownership = BetreeAuOwnershipImpl::new(2);
    let recovered = vec![1u32];
    proof {
        iau_seq_set_singleton(1);
        assert(recovered@ == seq![1u32]);
        assert(unique_iau_seq(recovered@));
        assert(ownership.all_aus() =~= Set::<AU>::empty());
    }
    let installed = ownership.install_recovered(&recovered);
    proof {
        assert(installed is Applied);
        assert(ownership.all_aus() =~= set![1nat]);
    }

    ownership.freeze_current();
    proof {
        assert(ownership.all_aus() =~= set![1nat]);
        assert(!ownership.active@.contains_key(2nat));
        assert(!ownership.retired@.contains_key(2nat));
    }
    let allocated = ownership.allocate(2);
    proof {
        assert(allocated is Applied);
        assert(ownership.frozen_aus() =~= set![1nat]);
        assert(!ownership.frozen_aus().contains(2nat));
    }
    let retired = ownership.retire(1);
    proof {
        assert(retired is Applied);
        assert(ownership.persistent_aus().contains(1nat));
        assert(ownership.frozen_aus().contains(1nat));
    }
    let first_reclaimed = ownership.commit_complete();
    proof {
        assert(iau_seq_set(first_reclaimed@) =~= Set::<AU>::empty());
        assert(first_reclaimed@.len() == 0) by {
            if first_reclaimed@.len() > 0 {
                assert(iau_seq_set(first_reclaimed@)
                    .contains(first_reclaimed@[0] as nat));
            }
        }
        assert(ownership.persistent_aus() =~= set![1nat]);
    }

    ownership.freeze_current();
    let second_reclaimed = ownership.commit_complete();
    proof {
        assert(iau_seq_set(second_reclaimed@) =~= set![1nat]);
        assert(ownership.persistent_aus() =~= set![2nat]);
    }
}

#[allow(dead_code)]
fn verify_branch_summary_snapshot_lifecycle() {
    let mut ownership = BranchSummaryOwnershipImpl::new(2);
    let summary = vec![10u32, 11u32];
    proof {
        iau_seq_set_pair(10, 11);
        assert(summary@ == seq![10u32, 11u32]);
        assert(unique_iau_seq(summary@));
        assert(iau_seq_set(summary@) =~= set![10nat, 11nat]);
        assert(ownership.all_summary_aus() =~= Set::<AU>::empty());
    }
    let installed = ownership.add_recovered(10, summary);
    proof {
        assert(installed is Applied);
        ownership.active_summary_map_dom();
        assert(ownership.active@.contains_key(10nat));
        assert(ownership.active_summary_aus() =~= set![10nat, 11nat]);
    }

    ownership.freeze_current();
    let retired = ownership.retire(10);
    proof {
        assert(retired is Applied);
        assert(ownership.active_summary_map().dom() =~= Set::<AU>::empty());
        ownership.active_summary_map_dom();
        assert(ownership.active_summary_aus() =~= Set::<AU>::empty()) by {
            assert forall |au: AU|
                #![trigger ownership.active_summary_aus().contains(au)]
                !ownership.active_summary_aus().contains(au) by {
                if ownership.active_summary_aus().contains(au) {
                    let root = choose |root: AU| #![auto]
                        ownership.active@.contains_key(root)
                        && ownership.active@[root].summary.contains(au);
                    assert(false);
                }
            }
        }
        assert(ownership.persistent_aus() =~= set![10nat, 11nat]);
        assert(ownership.frozen_aus() =~= set![10nat, 11nat]);
    }
    let first_reclaimed = ownership.commit_complete();
    proof {
        assert(iau_seq_set(first_reclaimed@) =~= Set::<AU>::empty());
        assert(first_reclaimed@.len() == 0) by {
            if first_reclaimed@.len() > 0 {
                assert(iau_seq_set(first_reclaimed@)
                    .contains(first_reclaimed@[0] as nat));
            }
        }
    }

    ownership.freeze_current();
    let second_reclaimed = ownership.commit_complete();
    proof {
        assert(iau_seq_set(second_reclaimed@) =~= set![10nat, 11nat]);
        assert(ownership.all_summary_aus() =~= Set::<AU>::empty());
    }
}

#[allow(dead_code)]
fn verify_combined_snapshot_reclamation() {
    let mut ownership = BranchBetreeOwnershipImpl::new(2);
    let betree_aus = vec![1u32];
    proof {
        iau_seq_set_singleton(1);
        assert(betree_aus@ == seq![1u32]);
        assert(unique_iau_seq(betree_aus@));
        assert(ownership.betree.all_aus() =~= Set::<AU>::empty());
        assert(ownership.betree.active@.dom() =~= Set::<AU>::empty());
        assert(ownership.betree.retired@.dom() =~= Set::<AU>::empty());
    }
    let installed_betree = ownership.betree.install_recovered(&betree_aus);
    proof { assert(installed_betree is Applied); }
    let summary = vec![10u32, 11u32];
    proof {
        iau_seq_set_pair(10, 11);
        assert(summary@ == seq![10u32, 11u32]);
        assert(unique_iau_seq(summary@));
        assert(iau_seq_set(summary@) =~= set![10nat, 11nat]);
        assert(ownership.betree.all_aus() =~= set![1nat]);
        assert(ownership.branches.all_summary_aus() =~= Set::<AU>::empty());
        assert(ownership.branches.all_summary_aus()
            .disjoint(iau_seq_set(summary@)));
    }
    let installed_branch = ownership.branches.add_recovered(10, summary);
    proof {
        assert(installed_branch is Applied);
        ownership.branches.active_summary_map_dom();
        assert(ownership.branches.active@.contains_key(10nat));
        assert(ownership.branches.all_summary_aus() =~= set![10nat, 11nat]);
        assert(ownership.betree.all_aus().disjoint(
            ownership.branches.all_summary_aus(),
        ));
        assert(ownership.wf());
        assert(ownership.persistent_aus()
            =~= set![1nat, 10nat, 11nat]);
        assert(ownership.current_durable_aus()
            =~= set![1nat, 10nat, 11nat]);
    }
    ownership.freeze_current();
    proof {
        assert(ownership.betree.active_aus().contains(1nat));
        ownership.branches.active_summary_map_dom();
        assert(ownership.branches.active@.contains_key(10nat));
        assert(ownership.frozen_aus()
            =~= set![1nat, 10nat, 11nat]);
    }
    let retired_betree = ownership.betree.retire(1);
    let retired_branch = ownership.branches.retire(10);
    proof {
        assert(retired_betree is Applied);
        assert(retired_branch is Applied);
        assert(ownership.wf());
        assert(ownership.betree.active_aus() =~= Set::<AU>::empty());
        ownership.branches.active_summary_map_dom();
        assert(ownership.branches.active_summary_aus()
            =~= Set::<AU>::empty()) by {
            assert forall |au: AU|
                #![trigger ownership.branches.active_summary_aus().contains(au)]
                !ownership.branches.active_summary_aus().contains(au) by {
                if ownership.branches.active_summary_aus().contains(au) {
                    let root = choose |root: AU| #![auto]
                        ownership.branches.active@.contains_key(root)
                        && ownership.branches.active@[root].summary.contains(au);
                    assert(false);
                }
            }
        }
        assert(ownership.current_durable_aus() =~= Set::<AU>::empty());
        assert(ownership.persistent_aus()
            =~= set![1nat, 10nat, 11nat]);
        assert(ownership.frozen_aus()
            =~= set![1nat, 10nat, 11nat]);
    }
    let first_reclaimed = ownership.commit_complete();
    proof {
        assert(iau_seq_set(first_reclaimed@) =~= Set::<AU>::empty());
        assert(first_reclaimed@.len() == 0) by {
            if first_reclaimed@.len() > 0 {
                assert(iau_seq_set(first_reclaimed@)
                    .contains(first_reclaimed@[0] as nat));
            }
        }
        assert(ownership.persistent_aus()
            =~= set![1nat, 10nat, 11nat]);
        assert(ownership.current_durable_aus() =~= Set::<AU>::empty());
    }
    ownership.freeze_current();
    proof {
        assert(ownership.persistent_aus()
            =~= set![1nat, 10nat, 11nat]);
        assert(ownership.frozen_aus() =~= Set::<AU>::empty());
        assert(ownership.current_durable_aus() =~= Set::<AU>::empty());
    }
    let second_reclaimed = ownership.commit_complete();
    proof {
        assert(iau_seq_set(second_reclaimed@) =~= set![1nat, 10nat, 11nat]);
        assert(unique_iau_seq(second_reclaimed@));
    }
}

}
