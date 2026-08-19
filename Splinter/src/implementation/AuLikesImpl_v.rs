// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_multisets_equal;
use vstd::assert_sets_equal;
use vstd::set_lib::*;

use crate::allocation_layer::Likes_v::AULikes;
use crate::disk::GenericDisk_v::{AU, IAU};

verus! {

#[derive(Clone, Copy, Debug)]
pub struct AuLikeEntry {
    pub au: IAU,
    pub count: u64,
}

pub struct AuLikeBucket {
    pub entries: Vec<AuLikeEntry>,
}

pub struct AuLikesImpl {
    pub buckets: Vec<AuLikeBucket>,
    pub bucket_count: u32,
}

#[derive(Debug)]
pub enum AuLikesUpdateResult {
    Applied { became_zero: Vec<IAU> },
    Noop,
}

pub open spec fn seq_to_au_likes(aus: Seq<IAU>) -> AULikes
    decreases aus.len()
{
    if aus.len() == 0 {
        AULikes::empty()
    } else {
        seq_to_au_likes(aus.drop_last()).insert(aus.last() as nat)
    }
}

pub open spec fn iau_seq_set(aus: Seq<IAU>) -> Set<AU> {
    Set::new(|au: AU| exists |i: int| #![auto]
        0 <= i < aus.len() && aus[i] as nat == au)
}

pub open spec fn unique_iau_seq(aus: Seq<IAU>) -> bool {
    forall |i: int, j: int| #![trigger aus[i], aus[j]]
        0 <= i < aus.len()
        && 0 <= j < aus.len()
        && aus[i] == aus[j]
        ==> i == j
}

pub open spec fn au_likes_delta_applicable(
    before: AULikes,
    removes: Seq<IAU>,
    adds: Seq<IAU>,
) -> bool {
    let remove_likes = seq_to_au_likes(removes);
    let target = before.sub(remove_likes).add(seq_to_au_likes(adds));
    &&& remove_likes <= before
    &&& forall |au: AU| #[trigger] target.count(au) <= u64::MAX as nat
}

pub proof fn seq_to_au_likes_push(aus: Seq<IAU>, au: IAU)
    ensures
        seq_to_au_likes(aus.push(au)) == seq_to_au_likes(aus).insert(au as nat),
{
    assert(aus.push(au).drop_last() == aus);
    assert(aus.push(au).last() == au);
}

pub proof fn seq_to_au_likes_dom(aus: Seq<IAU>)
    ensures seq_to_au_likes(aus).dom() =~= iau_seq_set(aus),
    decreases aus.len(),
{
    if aus.len() > 0 {
        let prefix = aus.drop_last();
        let last = aus.last();
        assert(prefix.push(last) == aus);
        seq_to_au_likes_dom(prefix);
        seq_to_au_likes_push(prefix, last);
        iau_seq_set_push(prefix, last);
        assert_sets_equal!(
            seq_to_au_likes(aus).dom(),
            seq_to_au_likes(prefix).dom().insert(last as nat),
            au => {}
        );
        assert(seq_to_au_likes(prefix).dom().insert(last as nat)
            =~= iau_seq_set(prefix).insert(last as nat));
        assert(iau_seq_set(aus)
            =~= iau_seq_set(prefix).insert(last as nat));
    } else {
        assert(seq_to_au_likes(aus).is_empty());
        assert(iau_seq_set(aus).is_empty());
    }
    assert_sets_equal!(
        seq_to_au_likes(aus).dom(),
        iau_seq_set(aus),
        au => {}
    );
}

proof fn seq_to_au_likes_len(aus: Seq<IAU>)
    ensures
        seq_to_au_likes(aus).len() == aus.len(),
    decreases aus.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    if aus.len() > 0 {
        seq_to_au_likes_len(aus.drop_last());
        assert(aus.drop_last().push(aus.last()) == aus);
        seq_to_au_likes_push(aus.drop_last(), aus.last());
    }
}

proof fn seq_to_au_likes_push_count(
    aus: Seq<IAU>,
    added: IAU,
    query: AU,
)
    ensures
        seq_to_au_likes(aus.push(added)).count(query)
            == seq_to_au_likes(aus).count(query)
                + if added as nat == query { 1nat } else { 0nat },
{
    seq_to_au_likes_push(aus, added);
    broadcast use vstd::multiset::group_multiset_axioms;
}

proof fn iau_seq_set_push(aus: Seq<IAU>, au: IAU)
    ensures
        iau_seq_set(aus.push(au)) =~= iau_seq_set(aus).insert(au as nat),
{
    assert_sets_equal!(
        iau_seq_set(aus.push(au)),
        iau_seq_set(aus).insert(au as nat),
        value => {
            if iau_seq_set(aus.push(au)).contains(value) {
                let i = choose |i: int| #![auto]
                    0 <= i < aus.push(au).len()
                    && aus.push(au)[i] as nat == value;
                if i < aus.len() {
                    assert(aus.push(au)[i] == aus[i]);
                } else {
                    assert(i == aus.len());
                }
            }
            if iau_seq_set(aus).insert(au as nat).contains(value) {
                if value == au as nat {
                    assert(aus.push(au)[aus.len() as int] == au);
                } else {
                    let i = choose |i: int| #![auto]
                        0 <= i < aus.len() && aus[i] as nat == value;
                    assert(aus.push(au)[i] == aus[i]);
                }
            }
        }
    );
}

proof fn unique_iau_seq_push(aus: Seq<IAU>, au: IAU)
    requires
        unique_iau_seq(aus),
        !iau_seq_set(aus).contains(au as nat),
    ensures
        unique_iau_seq(aus.push(au)),
{
    assert forall |i: int, j: int| #![trigger aus.push(au)[i], aus.push(au)[j]]
        0 <= i < aus.push(au).len()
        && 0 <= j < aus.push(au).len()
        && aus.push(au)[i] == aus.push(au)[j]
        implies i == j by {
        if i < aus.len() && j < aus.len() {
            assert(aus.push(au)[i] == aus[i]);
            assert(aus.push(au)[j] == aus[j]);
        } else if i < aus.len() {
            assert(j == aus.len());
            assert(iau_seq_set(aus).contains(aus[i] as nat));
        } else if j < aus.len() {
            assert(i == aus.len());
            assert(iau_seq_set(aus).contains(aus[j] as nat));
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct AuLikeDeltaEntry {
    au: IAU,
    removes: usize,
    adds: usize,
}

struct AuLikesDelta {
    entries: Vec<AuLikeDeltaEntry>,
}

impl AuLikesDelta {
    spec fn unique_aus(entries: Seq<AuLikeDeltaEntry>) -> bool {
        forall |i: int, j: int|
            #![trigger entries[i].au, entries[j].au]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i].au == entries[j].au
            ==> i == j
    }

    spec fn entries_nonempty(entries: Seq<AuLikeDeltaEntry>) -> bool {
        forall |i: int| #![trigger entries[i]]
            0 <= i < entries.len()
            ==> entries[i].removes > 0 || entries[i].adds > 0
    }

    spec fn removes_map(entries: Seq<AuLikeDeltaEntry>) -> Map<AU, nat>
        recommends Self::unique_aus(entries)
    {
        Map::new(
            |au: AU| exists |i: int| #![auto]
                0 <= i < entries.len()
                && entries[i].au as nat == au
                && entries[i].removes > 0,
            |au: AU| entries[choose |i: int| #![auto]
                0 <= i < entries.len()
                && entries[i].au as nat == au].removes as nat,
        )
    }

    spec fn adds_map(entries: Seq<AuLikeDeltaEntry>) -> Map<AU, nat>
        recommends Self::unique_aus(entries)
    {
        Map::new(
            |au: AU| exists |i: int| #![auto]
                0 <= i < entries.len()
                && entries[i].au as nat == au
                && entries[i].adds > 0,
            |au: AU| entries[choose |i: int| #![auto]
                0 <= i < entries.len()
                && entries[i].au as nat == au].adds as nat,
        )
    }

    spec fn wf(&self) -> bool {
        &&& Self::unique_aus(self.entries@)
        &&& Self::entries_nonempty(self.entries@)
    }

    spec fn removes(&self) -> AULikes {
        AULikes::from_map(Self::removes_map(self.entries@))
    }

    spec fn adds(&self) -> AULikes {
        AULikes::from_map(Self::adds_map(self.entries@))
    }

    proof fn delta_maps_finite(&self)
        requires
            self.wf(),
        ensures
            Self::removes_map(self.entries@).dom().finite(),
            Self::adds_map(self.entries@).dom().finite(),
    {
        let executable = Set::<AU>::new(|au: AU| au <= u32::MAX as nat);
        AuLikesImpl::executable_aus_finite();
        assert(Self::removes_map(self.entries@).dom() <= executable) by {
            assert forall |au: AU| #[trigger]
                Self::removes_map(self.entries@).dom().contains(au)
                implies executable.contains(au) by {
                let i = choose |i: int| #![auto]
                    0 <= i < self.entries@.len()
                    && self.entries@[i].au as nat == au
                    && self.entries@[i].removes > 0;
            }
        }
        assert(Self::adds_map(self.entries@).dom() <= executable) by {
            assert forall |au: AU| #[trigger]
                Self::adds_map(self.entries@).dom().contains(au)
                implies executable.contains(au) by {
                let i = choose |i: int| #![auto]
                    0 <= i < self.entries@.len()
                    && self.entries@[i].au as nat == au
                    && self.entries@[i].adds > 0;
            }
        }
        lemma_set_subset_finite(executable, Self::removes_map(self.entries@).dom());
        lemma_set_subset_finite(executable, Self::adds_map(self.entries@).dom());
    }

    proof fn map_count_ensures(&self, au: AU)
        requires
            self.wf(),
        ensures
            self.removes().count(au) == if Self::removes_map(self.entries@)
                .contains_key(au) {
                Self::removes_map(self.entries@)[au]
            } else { 0 },
            self.adds().count(au) == if Self::adds_map(self.entries@)
                .contains_key(au) {
                Self::adds_map(self.entries@)[au]
            } else { 0 },
    {
        self.delta_maps_finite();
        let removes = Self::removes_map(self.entries@);
        let adds = Self::adds_map(self.entries@);
        if removes.contains_key(au) {
            assert(self.removes().count(au) == removes[au]);
        } else {
            assert(self.removes().count(au) == 0);
        }
        if adds.contains_key(au) {
            assert(self.adds().count(au) == adds[au]);
        } else {
            assert(self.adds().count(au) == 0);
        }
    }

    proof fn entry_counts(&self, index: int)
        requires
            self.wf(),
            0 <= index < self.entries@.len(),
        ensures
            self.removes().count(self.entries@[index].au as nat)
                == self.entries@[index].removes as nat,
            self.adds().count(self.entries@[index].au as nat)
                == self.entries@[index].adds as nat,
    {



        self.map_count_ensures(self.entries@[index].au as nat);
        let entry = self.entries@[index];
        if entry.removes > 0 {
            assert(Self::removes_map(self.entries@).contains_key(entry.au as nat));
            assert(Self::removes_map(self.entries@)[entry.au as nat]
                == entry.removes as nat);
        } else {
            assert(!Self::removes_map(self.entries@).contains_key(entry.au as nat)) by {
                if Self::removes_map(self.entries@).contains_key(entry.au as nat) {
                    let i = choose |i: int| #![auto]
                        0 <= i < self.entries@.len()
                        && self.entries@[i].au == entry.au
                        && self.entries@[i].removes > 0;
                    assert(i == index);
                }
            }
        }
        if entry.adds > 0 {
            assert(Self::adds_map(self.entries@).contains_key(entry.au as nat));
            assert(Self::adds_map(self.entries@)[entry.au as nat]
                == entry.adds as nat);
        } else {
            assert(!Self::adds_map(self.entries@).contains_key(entry.au as nat)) by {
                if Self::adds_map(self.entries@).contains_key(entry.au as nat) {
                    let i = choose |i: int| #![auto]
                        0 <= i < self.entries@.len()
                        && self.entries@[i].au == entry.au
                        && self.entries@[i].adds > 0;
                    assert(i == index);
                }
            }
        }
    }

    proof fn absent_counts(&self, au: AU)
        requires
            self.wf(),
            forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                ==> self.entries@[i].au as nat != au,
        ensures
            self.removes().count(au) == 0,
            self.adds().count(au) == 0,
    {


        self.map_count_ensures(au);
        assert(!Self::removes_map(self.entries@).contains_key(au));
        assert(!Self::adds_map(self.entries@).contains_key(au));
    }

    proof fn target_count_for_entry(&self, before: AULikes, index: int)
        requires
            self.wf(),
            0 <= index < self.entries@.len(),
        ensures
            before.sub(self.removes()).add(self.adds()).count(
                self.entries@[index].au as nat,
            ) == if before.count(self.entries@[index].au as nat)
                    >= self.entries@[index].removes as nat {
                (before.count(self.entries@[index].au as nat)
                    - self.entries@[index].removes as nat) as nat
                    + self.entries@[index].adds as nat
            } else {
                self.entries@[index].adds as nat
            },
    {
        self.entry_counts(index);
        broadcast use vstd::multiset::group_multiset_axioms;
    }

    proof fn target_count_without_entry(&self, before: AULikes, au: AU)
        requires
            self.wf(),
            forall |i: int| #![trigger self.entries@[i]]
                0 <= i < self.entries@.len()
                ==> self.entries@[i].au as nat != au,
        ensures
            before.sub(self.removes()).add(self.adds()).count(au)
                == before.count(au),
    {
        self.absent_counts(au);
        broadcast use vstd::multiset::group_multiset_axioms;
    }

    spec fn zero_prefix(
        &self,
        before: AULikes,
        target: AULikes,
        end: nat,
    ) -> Set<AU> {
        Set::new(|au: AU| exists |i: int| #![auto]
            0 <= i < end
            && i < self.entries@.len()
            && self.entries@[i].au as nat == au
            && before.contains(au)
            && !target.contains(au))
    }

    proof fn zero_prefix_step(
        &self,
        before: AULikes,
        target: AULikes,
        end: nat,
    )
        requires
            self.wf(),
            end < self.entries@.len(),
        ensures
            self.zero_prefix(before, target, end + 1) =~=
                if before.contains(self.entries@[end as int].au as nat)
                    && !target.contains(self.entries@[end as int].au as nat) {
                    self.zero_prefix(before, target, end).insert(
                        self.entries@[end as int].au as nat,
                    )
                } else {
                    self.zero_prefix(before, target, end)
                },
    {


        let au = self.entries@[end as int].au as nat;
        assert_sets_equal!(
            self.zero_prefix(before, target, end + 1),
            if before.contains(au) && !target.contains(au) {
                self.zero_prefix(before, target, end).insert(au)
            } else {
                self.zero_prefix(before, target, end)
            },
            value => {
                if self.zero_prefix(before, target, end + 1).contains(value) {
                    let i = choose |i: int| #![auto]
                        0 <= i < end + 1
                        && i < self.entries@.len()
                        && self.entries@[i].au as nat == value
                        && before.contains(value)
                        && !target.contains(value);
                    if i < end {
                        assert(self.zero_prefix(before, target, end).contains(value));
                    } else {
                        assert(i == end);
                        assert(value == au);
                    }
                }
                if self.zero_prefix(before, target, end).contains(value) {
                    let i = choose |i: int| #![auto]
                        0 <= i < end
                        && i < self.entries@.len()
                        && self.entries@[i].au as nat == value
                        && before.contains(value)
                        && !target.contains(value);
                    assert(i < end + 1);
                }
                if value == au && before.contains(au) && !target.contains(au) {
                    assert(self.zero_prefix(before, target, end + 1).contains(value));
                }
            }
        );
    }

    proof fn zero_prefix_complete(
        &self,
        before: AULikes,
        target: AULikes,
    )
        requires
            self.wf(),
            target == before.sub(self.removes()).add(self.adds()),
        ensures
            self.zero_prefix(before, target, self.entries@.len()) =~=
                before.dom() - target.dom(),
    {

        assert_sets_equal!(
            self.zero_prefix(before, target, self.entries@.len()),
            before.dom() - target.dom(),
            au => {
                if self.zero_prefix(before, target, self.entries@.len()).contains(au) {
                    assert(before.count(au) > 0);
                    assert(target.count(au) == 0);
                }
                if before.dom().contains(au) && !target.dom().contains(au) {
                    if forall |i: int| #![trigger self.entries@[i]]
                        0 <= i < self.entries@.len()
                        ==> self.entries@[i].au as nat != au {
                        self.target_count_without_entry(before, au);
                        assert(false);
                    }
                    let i = choose |i: int| #![auto]
                        0 <= i < self.entries@.len()
                        && self.entries@[i].au as nat == au;
                    assert(self.zero_prefix(
                        before,
                        target,
                        self.entries@.len(),
                    ).contains(au));
                }
            }
        );
    }

    fn new() -> (out: Self)
        ensures
            out.wf(),
            out.removes() == AULikes::empty(),
            out.adds() == AULikes::empty(),
    {
        let out = Self { entries: Vec::new() };
        proof {
            out.delta_maps_finite();
            assert_multisets_equal!(out.removes(), AULikes::empty());
            assert_multisets_equal!(out.adds(), AULikes::empty());
        }
        out
    }

    fn from_sequences(removes: &Vec<IAU>, adds: &Vec<IAU>) -> (out: Self)
        ensures
            out.wf(),
            out.removes() == seq_to_au_likes(removes@),
            out.adds() == seq_to_au_likes(adds@),
    {
        let mut delta = Self::new();
        let mut index = 0usize;
        while index < removes.len()
            invariant
                delta.wf(),
                index <= removes.len(),
                delta.removes() == seq_to_au_likes(removes@.take(index as int)),
                delta.adds() == AULikes::empty(),
            decreases removes.len() - index,
        {
            let au = removes[index];
            proof {
                seq_to_au_likes_len(removes@.take(index as int));
                assert(delta.removes().len() == index as nat);
                assert(index < usize::MAX);
            }
            delta.record(au, true);
            proof {
                assert(removes@.take(index as int + 1)
                    == removes@.take(index as int).push(au));
                seq_to_au_likes_push(removes@.take(index as int), au);
            }
            index += 1;
        }

        proof {
            assert(index == removes@.len());
            assert(removes@.take(index as int) == removes@);
            assert(delta.removes() == seq_to_au_likes(removes@));
        }

        index = 0;
        while index < adds.len()
            invariant
                delta.wf(),
                index <= adds.len(),
                delta.removes() == seq_to_au_likes(removes@),
                delta.adds() == seq_to_au_likes(adds@.take(index as int)),
            decreases adds.len() - index,
        {
            let au = adds[index];
            proof {
                seq_to_au_likes_len(adds@.take(index as int));
                assert(delta.adds().len() == index as nat);
                assert(index < usize::MAX);
            }
            delta.record(au, false);
            proof {
                assert(adds@.take(index as int + 1)
                    == adds@.take(index as int).push(au));
                seq_to_au_likes_push(adds@.take(index as int), au);
            }
            index += 1;
        }
        proof {
            assert(index == adds@.len());
            assert(adds@.take(index as int) == adds@);
            assert(delta.adds() == seq_to_au_likes(adds@));
        }
        delta
    }

    fn record(&mut self, au: IAU, removing: bool)
        requires
            old(self).wf(),
            if removing {
                old(self).removes().len() < usize::MAX as nat
            } else {
                old(self).adds().len() < usize::MAX as nat
            },
        ensures
            self.wf(),
            self.removes() == if removing {
                old(self).removes().insert(au as nat)
            } else {
                old(self).removes()
            },
            self.adds() == if removing {
                old(self).adds()
            } else {
                old(self).adds().insert(au as nat)
            },
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
                let old_entry = self.entries[index];
                proof {
                    self.entry_counts(index as int);
                    broadcast use vstd::multiset::group_multiset_axioms;
                    if removing {
                        assert(old_entry.removes as nat
                            <= self.removes().len());
                        assert(old_entry.removes < usize::MAX);
                    } else {
                        assert(old_entry.adds as nat <= self.adds().len());
                        assert(old_entry.adds < usize::MAX);
                    }
                }
                if removing {
                    self.entries[index] = AuLikeDeltaEntry {
                        removes: old_entry.removes + 1,
                        ..old_entry
                    };
                } else {
                    self.entries[index] = AuLikeDeltaEntry {
                        adds: old_entry.adds + 1,
                        ..old_entry
                    };
                }
                proof {



                    let new_entry = self.entries@[index as int];
                    assert(self.entries@ == old_entries.update(index as int, new_entry));
                    assert(Self::unique_aus(self.entries@));
                    assert(Self::entries_nonempty(self.entries@));
                    let old_removes = Self::removes_map(old_entries);
                    let old_adds = Self::adds_map(old_entries);
                    let new_removes = Self::removes_map(self.entries@);
                    let new_adds = Self::adds_map(self.entries@);
                    assert_maps_equal!(new_removes, if removing {
                        old_removes.insert(au as nat, old_entry.removes as nat + 1)
                    } else { old_removes }, other_au => {
                        if old_removes.contains_key(other_au) {
                            let old_i = choose |i: int| #![auto]
                                0 <= i < old_entries.len()
                                && old_entries[i].au as nat == other_au
                                && old_entries[i].removes > 0;
                            assert(self.entries@[old_i].au as nat == other_au);
                            assert(self.entries@[old_i].removes > 0);
                            assert(new_removes.contains_key(other_au));
                        }
                        if removing && other_au == au as nat {
                            assert(self.entries@[index as int].removes > 0);
                            assert(new_removes.contains_key(other_au));
                        }
                    });
                    assert_maps_equal!(new_adds, if removing {
                        old_adds
                    } else {
                        old_adds.insert(au as nat, old_entry.adds as nat + 1)
                    }, other_au => {
                        if old_adds.contains_key(other_au) {
                            let old_i = choose |i: int| #![auto]
                                0 <= i < old_entries.len()
                                && old_entries[i].au as nat == other_au
                                && old_entries[i].adds > 0;
                            assert(self.entries@[old_i].au as nat == other_au);
                            assert(self.entries@[old_i].adds > 0);
                            assert(new_adds.contains_key(other_au));
                        }
                        if !removing && other_au == au as nat {
                            assert(self.entries@[index as int].adds > 0);
                            assert(new_adds.contains_key(other_au));
                        }
                    });
                    self.delta_maps_finite();
                    old(self).delta_maps_finite();
                    broadcast use vstd::multiset::group_multiset_axioms;
                    assert_multisets_equal!(self.removes(), if removing {
                        old(self).removes().insert(au as nat)
                    } else { old(self).removes() }, other_au => { });
                    assert_multisets_equal!(self.adds(), if removing {
                        old(self).adds()
                    } else { old(self).adds().insert(au as nat) }, other_au => { });
                }
                return;
            }
            index += 1;
        }

        let entry = if removing {
            AuLikeDeltaEntry { au, removes: 1, adds: 0 }
        } else {
            AuLikeDeltaEntry { au, removes: 0, adds: 1 }
        };
        self.entries.push(entry);
        proof {



            assert(Self::unique_aus(self.entries@)) by {
                assert forall |i: int, j: int|
                    #![trigger self.entries@[i].au, self.entries@[j].au]
                    0 <= i < self.entries@.len()
                    && 0 <= j < self.entries@.len()
                    && self.entries@[i].au == self.entries@[j].au
                    implies i == j by {
                    if i < old_entries.len() && j < old_entries.len() {
                    } else if i < old_entries.len() {
                        assert(j == old_entries.len());
                        assert(self.entries@[j] == entry);
                        assert(i < index);
                    } else if j < old_entries.len() {
                        assert(i == old_entries.len());
                        assert(self.entries@[i] == entry);
                        assert(j < index);
                    }
                }
            }
            assert(Self::entries_nonempty(self.entries@));
            let old_removes = Self::removes_map(old_entries);
            let old_adds = Self::adds_map(old_entries);
            let new_removes = Self::removes_map(self.entries@);
            let new_adds = Self::adds_map(self.entries@);
            assert_maps_equal!(new_removes, if removing {
                old_removes.insert(au as nat, 1)
            } else { old_removes }, other_au => {
                if old_removes.contains_key(other_au) {
                    let old_i = choose |i: int| #![auto]
                        0 <= i < old_entries.len()
                        && old_entries[i].au as nat == other_au
                        && old_entries[i].removes > 0;
                    assert(self.entries@[old_i] == old_entries[old_i]);
                    assert(new_removes.contains_key(other_au));
                }
                if removing && other_au == au as nat {
                    assert(self.entries@[old_entries.len() as int] == entry);
                    assert(new_removes.contains_key(other_au));
                }
            });
            assert_maps_equal!(new_adds, if removing {
                old_adds
            } else {
                old_adds.insert(au as nat, 1)
            }, other_au => {
                if old_adds.contains_key(other_au) {
                    let old_i = choose |i: int| #![auto]
                        0 <= i < old_entries.len()
                        && old_entries[i].au as nat == other_au
                        && old_entries[i].adds > 0;
                    assert(self.entries@[old_i] == old_entries[old_i]);
                    assert(new_adds.contains_key(other_au));
                }
                if !removing && other_au == au as nat {
                    assert(self.entries@[old_entries.len() as int] == entry);
                    assert(new_adds.contains_key(other_au));
                }
            });
            self.delta_maps_finite();
            old(self).delta_maps_finite();
            broadcast use vstd::multiset::group_multiset_axioms;
            assert_multisets_equal!(self.removes(), if removing {
                old(self).removes().insert(au as nat)
            } else { old(self).removes() }, other_au => { });
            assert_multisets_equal!(self.adds(), if removing {
                old(self).adds()
            } else { old(self).adds().insert(au as nat) }, other_au => { });
        }
    }
}

impl AuLikeBucket {
    pub open spec fn unique_aus(entries: Seq<AuLikeEntry>) -> bool {
        forall |i: int, j: int|
            #![trigger entries[i].au, entries[j].au]
            0 <= i < entries.len()
            && 0 <= j < entries.len()
            && entries[i].au == entries[j].au
            ==> i == j
    }

    pub open spec fn positive_counts(entries: Seq<AuLikeEntry>) -> bool {
        forall |i: int| #![trigger entries[i]]
            0 <= i < entries.len() ==> entries[i].count > 0
    }

    pub open spec fn entries_map(entries: Seq<AuLikeEntry>) -> Map<AU, nat>
        recommends Self::unique_aus(entries)
    {
        Map::new(
            |au: AU| exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].au as nat == au,
            |au: AU| entries[choose |i: int| #![auto]
                0 <= i < entries.len() && entries[i].au as nat == au].count as nat,
        )
    }

    pub open spec fn wf(&self) -> bool {
        &&& Self::unique_aus(self.entries@)
        &&& Self::positive_counts(self.entries@)
    }

    pub proof fn entries_map_index(entries: Seq<AuLikeEntry>, i: int)
        requires
            Self::unique_aus(entries),
            0 <= i < entries.len(),
        ensures
            Self::entries_map(entries).contains_key(entries[i].au as nat),
            Self::entries_map(entries)[entries[i].au as nat]
                == entries[i].count as nat,
    {
    }

    pub proof fn entries_map_index_for_au(entries: Seq<AuLikeEntry>, au: AU) -> (i: int)
        requires
            Self::unique_aus(entries),
            Self::entries_map(entries).contains_key(au),
        ensures
            0 <= i < entries.len(),
            entries[i].au as nat == au,
            Self::entries_map(entries)[au] == entries[i].count as nat,
    {
        let i = choose |i: int| #![auto]
            0 <= i < entries.len() && entries[i].au as nat == au;
        Self::entries_map_index(entries, i);
        i
    }

    proof fn entries_map_after_set(
        old_entries: Seq<AuLikeEntry>,
        index: int,
        entry: AuLikeEntry,
    )
        requires
            Self::unique_aus(old_entries),
            0 <= index < old_entries.len(),
            old_entries[index].au == entry.au,
            entry.count > 0,
        ensures
            Self::unique_aus(old_entries.update(index, entry)),
            Self::positive_counts(old_entries) ==>
                Self::positive_counts(old_entries.update(index, entry)),
            Self::entries_map(old_entries.update(index, entry))
                == Self::entries_map(old_entries).insert(entry.au as nat, entry.count as nat),
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
        if Self::positive_counts(old_entries) {
            assert forall |i: int| #![trigger new_entries[i]]
                0 <= i < new_entries.len()
                implies new_entries[i].count > 0 by {
                if i != index {
                    assert(new_entries[i] == old_entries[i]);
                }
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(entry.au as nat, entry.count as nat),
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
        old_entries: Seq<AuLikeEntry>,
        entry: AuLikeEntry,
    )
        requires
            Self::unique_aus(old_entries),
            Self::positive_counts(old_entries),
            !Self::entries_map(old_entries).contains_key(entry.au as nat),
            entry.count > 0,
        ensures
            Self::unique_aus(old_entries.push(entry)),
            Self::positive_counts(old_entries.push(entry)),
            Self::entries_map(old_entries.push(entry))
                == Self::entries_map(old_entries).insert(entry.au as nat, entry.count as nat),
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
                assert(Self::entries_map(old_entries).contains_key(old_entries[j].au as nat));
            } else if i < old_entries.len() && j == old_entries.len() {
                assert(Self::entries_map(old_entries).contains_key(old_entries[i].au as nat));
            }
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).insert(entry.au as nat, entry.count as nat),
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

    proof fn entries_map_after_remove(old_entries: Seq<AuLikeEntry>, index: int)
        requires
            Self::unique_aus(old_entries),
            Self::positive_counts(old_entries),
            0 <= index < old_entries.len(),
        ensures
            Self::unique_aus(old_entries.remove(index)),
            Self::positive_counts(old_entries.remove(index)),
            Self::entries_map(old_entries.remove(index))
                == Self::entries_map(old_entries).remove(old_entries[index].au as nat),
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
        assert forall |i: int| #![trigger new_entries[i]]
            0 <= i < new_entries.len()
            implies new_entries[i].count > 0 by {
            let old_i = if i < index { i } else { i + 1 };
            assert(new_entries[i] == old_entries[old_i]);
        }
        assert_maps_equal!(
            Self::entries_map(new_entries),
            Self::entries_map(old_entries).remove(old_entries[index].au as nat),
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
            out@ == Map::<AU, nat>::empty(),
            out.entries@.len() == 0,
    {
        let out = Self { entries: Vec::new() };
        assert(out@ == Map::<AU, nat>::empty());
        out
    }

    fn count(&self, au: IAU) -> (out: u64)
        requires
            self.wf(),
        ensures
            out as nat == if self@.contains_key(au as nat) {
                self@[au as nat]
            } else {
                0
            },
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
                return self.entries[index].count;
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
        0
    }

    fn set_count(&mut self, au: IAU, count: u64)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == if count == 0 {
                old(self)@.remove(au as nat)
            } else {
                old(self)@.insert(au as nat, count as nat)
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
                if count == 0 {
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
                } else {
                    self.entries[index] = AuLikeEntry { au, count };
                    proof {
                        assert(self.entries@ == old_entries.update(
                            index as int,
                            AuLikeEntry { au, count },
                        ));
                        Self::entries_map_after_set(
                            old_entries,
                            index as int,
                            AuLikeEntry { au, count },
                        );
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
                }
                return;
            }
            index += 1;
        }

        if count == 0 {
            proof {
                assert(!self@.contains_key(au as nat)) by {
                    if self@.contains_key(au as nat) {
                        let i = Self::entries_map_index_for_au(old_entries, au as nat);
                        assert(i < index);
                        assert(self.entries@[i].au == au);
                    }
                }
                assert(self@ == old(self)@.remove(au as nat));
            }
            return;
        }

        proof {
            assert(!Self::entries_map(old_entries).contains_key(au as nat)) by {
                if Self::entries_map(old_entries).contains_key(au as nat) {
                    let i = Self::entries_map_index_for_au(old_entries, au as nat);
                    assert(i < index);
                    assert(self.entries@[i].au == au);
                }
            }
        }
        self.entries.push(AuLikeEntry { au, count });
        proof {
            Self::entries_map_after_push(old_entries, AuLikeEntry { au, count });
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
    }
}

impl View for AuLikeBucket {
    type V = Map<AU, nat>;

    open spec fn view(&self) -> Map<AU, nat> {
        Self::entries_map(self.entries@)
    }
}

impl AuLikesImpl {
    pub open spec fn bucket_index(au: AU, bucket_count: nat) -> nat
        recommends bucket_count > 0
    {
        au % bucket_count
    }

    pub open spec fn buckets_count_map(
        buckets: Seq<AuLikeBucket>,
        bucket_count: nat,
    ) -> Map<AU, nat>
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
            0 <= bucket < self.buckets@.len() ==> self.buckets@[bucket].wf()
        &&& forall |bucket: int, entry: int|
            #![trigger self.buckets@[bucket].entries@[entry]]
            0 <= bucket < self.buckets@.len()
            && 0 <= entry < self.buckets@[bucket].entries@.len()
            ==> Self::bucket_index(
                self.buckets@[bucket].entries@[entry].au as nat,
                self.bucket_count as nat,
            ) == bucket
    }

    proof fn executable_aus_finite()
        ensures
            Set::<AU>::new(|au: AU| au <= u32::MAX as nat).finite(),
    {
        let int_range = set_int_range(0, u32::MAX as int + 1);
        let nat_range = Set::<AU>::new(|au: AU| au <= u32::MAX as nat);
        let mapped = int_range.map(|i: int| i as nat);
        lemma_int_range(0, u32::MAX as int + 1);
        int_range.lemma_map_finite(|i: int| i as nat);
        assert(nat_range =~= mapped) by {
            assert forall |au: AU| #[trigger] nat_range.contains(au)
                implies mapped.contains(au) by {
                assert(int_range.contains(au as int));
            }
            assert forall |au: AU| #[trigger] mapped.contains(au)
                implies nat_range.contains(au) by {
                let i = choose |i: int| int_range.contains(i) && i as nat == au;
                assert(0 <= i);
                assert(i < u32::MAX as int + 1);
            }
        }
    }

    proof fn count_map_finite(&self)
        requires
            self.wf(),
        ensures
            Self::buckets_count_map(self.buckets@, self.bucket_count as nat).dom().finite(),
    {
        let count_map = Self::buckets_count_map(self.buckets@, self.bucket_count as nat);
        let executable = Set::<AU>::new(|au: AU| au <= u32::MAX as nat);
        Self::executable_aus_finite();
        assert(count_map.dom() <= executable) by {
            assert forall |au: AU| #[trigger] count_map.dom().contains(au)
                implies executable.contains(au) by {
                let bucket = Self::bucket_index(au, self.bucket_count as nat) as int;
                assert(self.buckets@[bucket]@.contains_key(au));
                let index = AuLikeBucket::entries_map_index_for_au(
                    self.buckets@[bucket].entries@,
                    au,
                );
                assert(self.buckets@[bucket].entries@[index].au as nat == au);
            }
        }
        lemma_set_subset_finite(executable, count_map.dom());
    }

    proof fn view_count_matches_map(&self, au: AU)
        requires
            self.wf(),
        ensures
            self@.count(au) == if Self::buckets_count_map(
                self.buckets@,
                self.bucket_count as nat,
            ).contains_key(au) {
                Self::buckets_count_map(
                    self.buckets@,
                    self.bucket_count as nat,
                )[au]
            } else {
                0
            },
    {
        self.count_map_finite();
        let count_map = Self::buckets_count_map(self.buckets@, self.bucket_count as nat);
        if count_map.contains_key(au) {
            assert(self@.count(au) == count_map[au]);
        } else {
            assert(self@.count(au) == 0);
        }
    }

    pub proof fn view_counts_bounded(&self)
        requires
            self.wf(),
        ensures
            forall |au: AU| #[trigger] self@.count(au) <= u64::MAX as nat,
    {
        assert forall |au: AU| #[trigger] self@.count(au) <= u64::MAX as nat by {
            self.view_count_matches_map(au);
            let count_map = Self::buckets_count_map(
                self.buckets@,
                self.bucket_count as nat,
            );
            if count_map.contains_key(au) {
                let bucket = Self::bucket_index(au, self.bucket_count as nat) as int;
                let entry = AuLikeBucket::entries_map_index_for_au(
                    self.buckets@[bucket].entries@,
                    au,
                );
                assert(count_map[au]
                    == self.buckets@[bucket].entries@[entry].count as nat);
            }
        }
    }

    proof fn buckets_update_refines(
        old_buckets: Seq<AuLikeBucket>,
        new_buckets: Seq<AuLikeBucket>,
        bucket_count: nat,
        bucket: int,
        au: AU,
        count: nat,
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
            new_buckets[bucket]@ == if count == 0 {
                old_buckets[bucket]@.remove(au)
            } else {
                old_buckets[bucket]@.insert(au, count)
            },
            forall |i: int| #![trigger new_buckets[i]]
                0 <= i < new_buckets.len() && i != bucket
                ==> new_buckets[i]@ == old_buckets[i]@,
        ensures
            Self::buckets_count_map(new_buckets, bucket_count) == if count == 0 {
                Self::buckets_count_map(old_buckets, bucket_count).remove(au)
            } else {
                Self::buckets_count_map(old_buckets, bucket_count).insert(au, count)
            },
    {
        assert_maps_equal!(
            Self::buckets_count_map(new_buckets, bucket_count),
            if count == 0 {
                Self::buckets_count_map(old_buckets, bucket_count).remove(au)
            } else {
                Self::buckets_count_map(old_buckets, bucket_count).insert(au, count)
            },
            other_au => {
                let other_bucket = Self::bucket_index(other_au, bucket_count) as int;
                if other_au == au {
                    assert(other_bucket == bucket);
                } else if other_bucket == bucket {
                } else {
                    assert(new_buckets[other_bucket]@ == old_buckets[other_bucket]@);
                }
            }
        );
    }

    fn exec_bucket_index(au: IAU, bucket_count: u32) -> (out: usize)
        requires
            bucket_count > 0,
        ensures
            out as nat == Self::bucket_index(au as nat, bucket_count as nat),
            out < bucket_count as usize,
    {
        (au % bucket_count) as usize
    }

    fn empty_buckets(bucket_count: u32) -> (out: Vec<AuLikeBucket>)
        requires
            bucket_count > 0,
        ensures
            out@.len() == bucket_count as nat,
            forall |i: int| #![trigger out@[i]]
                0 <= i < out@.len()
                ==> out@[i].wf() && out@[i]@ == Map::<AU, nat>::empty(),
            forall |i: int| #![trigger out@[i]]
                0 <= i < out@.len() ==> out@[i].entries@.len() == 0,
    {
        let mut out: Vec<AuLikeBucket> = Vec::new();
        let mut index = 0usize;
        while index < bucket_count as usize
            invariant
                index <= bucket_count as usize,
                out@.len() == index,
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len()
                    ==> out@[i].wf() && out@[i]@ == Map::<AU, nat>::empty(),
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len() ==> out@[i].entries@.len() == 0,
            decreases bucket_count as usize - index,
        {
            let bucket = AuLikeBucket::new();
            out.push(bucket);
            proof {
                assert(out@[index as int].entries@.len() == 0);
            }
            index += 1;
        }
        out
    }

    pub fn new(bucket_count: u32) -> (out: Self)
        requires
            bucket_count > 0,
        ensures
            out.wf(),
            out@ == AULikes::empty(),
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
            out.count_map_finite();
            assert_multisets_equal!(out@, AULikes::empty(), au => {
                assert(!Self::buckets_count_map(out.buckets@, out.bucket_count as nat)
                    .contains_key(au));
            });
        }
        out
    }

    pub fn count(&self, au: IAU) -> (out: u64)
        requires
            self.wf(),
        ensures
            out as nat == self@.count(au as nat),
    {
        let bucket = Self::exec_bucket_index(au, self.bucket_count);
        let out = self.buckets[bucket].count(au);
        proof {
            self.view_count_matches_map(au as nat);
        }
        out
    }

    pub fn contains(&self, au: IAU) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self@.contains(au as nat),
    {
        self.count(au) != 0
    }

    pub fn is_empty(&self) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self@.is_empty(),
    {
        let mut bucket = 0usize;
        while bucket < self.buckets.len()
            invariant
                self.wf(),
                bucket <= self.buckets.len(),
                forall |i: int| #![trigger self.buckets@[i]]
                    0 <= i < bucket ==> self.buckets@[i].entries@.len() == 0,
            decreases self.buckets.len() - bucket,
        {
            if self.buckets[bucket].entries.len() != 0 {
                proof {
                    let entry = self.buckets@[bucket as int].entries@[0];
                    AuLikeBucket::entries_map_index(
                        self.buckets@[bucket as int].entries@,
                        0,
                    );
                    self.count_map_finite();
                    assert(self@.contains(entry.au as nat));
                }
                return false;
            }
            bucket += 1;
        }
        proof {
            self.count_map_finite();
            assert(self@ =~= AULikes::empty()) by {
                assert forall |au: AU| self@.count(au) == 0 by {
                    let selected = Self::bucket_index(au, self.bucket_count as nat) as int;
                    assert(self.buckets@[selected].entries@.len() == 0);
                    assert(!Self::buckets_count_map(self.buckets@, self.bucket_count as nat)
                        .contains_key(au));
                }
            }
        }
        true
    }

    fn set_count(&mut self, au: IAU, count: u64)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            self@ == old(self)@.update(au as nat, count as nat),
    {
        let bucket = Self::exec_bucket_index(au, self.bucket_count);
        let ghost old_buckets = self.buckets@;
        let mut selected = self.buckets.remove(bucket);
        selected.set_count(au, count);
        self.buckets.insert(bucket, selected);
        proof {
            assert forall |i: int| #![trigger self.buckets@[i]]
                0 <= i < self.buckets@.len() && i != bucket
                implies self.buckets@[i]@ == old_buckets[i]@ by { }
            assert forall |b: int, e: int|
                #![trigger self.buckets@[b].entries@[e]]
                0 <= b < self.buckets@.len()
                && 0 <= e < self.buckets@[b].entries@.len()
                implies Self::bucket_index(
                    self.buckets@[b].entries@[e].au as nat,
                    self.bucket_count as nat,
                ) == b by {
                if b == bucket {
                    if self.buckets@[b].entries@[e].au == au {
                    } else {
                        assert(exists |old_e: int| #![auto]
                            0 <= old_e < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_e].au
                                == self.buckets@[b].entries@[e].au);
                        let old_e = choose |old_e: int| #![auto]
                            0 <= old_e < old_buckets[b].entries@.len()
                            && old_buckets[b].entries@[old_e].au
                                == self.buckets@[b].entries@[e].au;
                        assert(Self::bucket_index(
                            old_buckets[b].entries@[old_e].au as nat,
                            self.bucket_count as nat,
                        ) == b);
                    }
                } else {
                    assert(self.buckets@[b].entries@ == old_buckets[b].entries@);
                }
            }
            Self::buckets_update_refines(
                old_buckets,
                self.buckets@,
                self.bucket_count as nat,
                bucket as int,
                au as nat,
                count as nat,
            );
            old(self).count_map_finite();
            self.count_map_finite();
            let old_map = Self::buckets_count_map(
                old(self).buckets@,
                old(self).bucket_count as nat,
            );
            let new_map = Self::buckets_count_map(
                self.buckets@,
                self.bucket_count as nat,
            );
            assert(new_map == if count == 0 {
                old_map.remove(au as nat)
            } else {
                old_map.insert(au as nat, count as nat)
            });
            broadcast use vstd::multiset::group_multiset_properties;
            assert_multisets_equal!(
                self@,
                old(self)@.update(au as nat, count as nat),
                other_au => {
                    self.view_count_matches_map(other_au);
                    old(self).view_count_matches_map(other_au);
                    if other_au == au as nat {
                        if count == 0 {
                            assert(!new_map.contains_key(other_au));
                            assert(self@.count(other_au) == 0);
                        } else {
                            assert(new_map[other_au] == count as nat);
                            assert(self@.count(other_au) == count as nat);
                        }
                    } else {
                        if old_map.contains_key(other_au) {
                            assert(new_map.contains_key(other_au));
                            assert(new_map[other_au] == old_map[other_au]);
                        } else {
                            assert(!new_map.contains_key(other_au));
                        }
                    }
                }
            );
        }
    }

    pub fn apply_delta(
        &mut self,
        removes: &Vec<IAU>,
        adds: &Vec<IAU>,
    ) -> (result: AuLikesUpdateResult)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            (result is Applied) <==> au_likes_delta_applicable(
                old(self)@,
                removes@,
                adds@,
            ),
            match result {
                AuLikesUpdateResult::Applied { became_zero } => {
                    &&& self@ == old(self)@.sub(seq_to_au_likes(removes@))
                        .add(seq_to_au_likes(adds@))
                    &&& unique_iau_seq(became_zero@)
                    &&& iau_seq_set(became_zero@) =~=
                        old(self)@.dom() - self@.dom()
                },
                AuLikesUpdateResult::Noop => {
                    &&& self.buckets@ == old(self).buckets@
                    &&& self.bucket_count == old(self).bucket_count
                    &&& self@ == old(self)@
                },
            },
    {
        proof { self.view_counts_bounded(); }
        let delta = AuLikesDelta::from_sequences(removes, adds);

        let ghost initial = self@;
        let ghost target = initial.sub(delta.removes()).add(delta.adds());
        let mut became_zero = Vec::<IAU>::new();
        let mut index = 0usize;
        while index < delta.entries.len()
            invariant
                self.wf(),
                self.buckets@ == old(self).buckets@,
                self.bucket_count == old(self).bucket_count,
                self@ == initial,
                forall |au: AU| #[trigger] initial.count(au) <= u64::MAX as nat,
                delta.wf(),
                index <= delta.entries.len(),
                unique_iau_seq(became_zero@),
                iau_seq_set(became_zero@) =~=
                    delta.zero_prefix(initial, target, index as nat),
                forall |i: int| #![trigger delta.entries@[i]]
                    0 <= i < index
                    ==> initial.count(delta.entries@[i].au as nat)
                            >= delta.entries@[i].removes as nat
                        && target.count(delta.entries@[i].au as nat)
                            <= u64::MAX as nat,
            decreases delta.entries.len() - index,
        {
            let entry = delta.entries[index];
            let remove_count = entry.removes as u64;
            let add_count = entry.adds as u64;
            let current = self.count(entry.au);
            if current < remove_count {
                proof {
                    delta.entry_counts(index as int);
                    assert(delta.removes().count(entry.au as nat)
                        > initial.count(entry.au as nat));
                    assert(!(delta.removes() <= initial));
                    assert(delta.removes() == seq_to_au_likes(removes@));
                    assert(!au_likes_delta_applicable(initial, removes@, adds@));
                }
                return AuLikesUpdateResult::Noop;
            }
            let after_removes = current - remove_count;
            if add_count > u64::MAX - after_removes {
                proof {
                    delta.target_count_for_entry(initial, index as int);
                    assert(target.count(entry.au as nat) > u64::MAX as nat);
                    assert(delta.removes() == seq_to_au_likes(removes@));
                    assert(delta.adds() == seq_to_au_likes(adds@));
                    assert(!au_likes_delta_applicable(initial, removes@, adds@));
                }
                return AuLikesUpdateResult::Noop;
            }
            let final_count = after_removes + add_count;
            proof {
                delta.target_count_for_entry(initial, index as int);
                assert(initial.count(entry.au as nat) == current as nat);
                assert(target.count(entry.au as nat) == final_count as nat);
                delta.zero_prefix_step(initial, target, index as nat);
            }
            if current > 0 && final_count == 0 {
                proof {
                    assert(!iau_seq_set(became_zero@).contains(entry.au as nat)) by {
                        if iau_seq_set(became_zero@).contains(entry.au as nat) {
                            assert(delta.zero_prefix(
                                initial,
                                target,
                                index as nat,
                            ).contains(entry.au as nat));

                            let prior = choose |i: int| #![auto]
                                0 <= i < index
                                && i < delta.entries@.len()
                                && delta.entries@[i].au == entry.au
                                && initial.contains(entry.au as nat)
                                && !target.contains(entry.au as nat);

                            assert(prior == index);
                        }
                    }
                    unique_iau_seq_push(became_zero@, entry.au);
                    iau_seq_set_push(became_zero@, entry.au);
                }
                became_zero.push(entry.au);
            }
            proof {
                assert(initial.contains(entry.au as nat) && !target.contains(entry.au as nat)
                    <==> current > 0 && final_count == 0);
                assert(iau_seq_set(became_zero@) =~=
                    delta.zero_prefix(initial, target, index as nat + 1));
            }
            index += 1;
        }

        proof {
            assert(index == delta.entries@.len());
            delta.zero_prefix_complete(initial, target);
            assert(iau_seq_set(became_zero@) =~= initial.dom() - target.dom());
            assert forall |au: AU| #[trigger]
                delta.removes().count(au) <= initial.count(au) by {
                if forall |i: int| #![trigger delta.entries@[i]]
                    0 <= i < delta.entries@.len()
                    ==> delta.entries@[i].au as nat != au {
                    delta.absent_counts(au);
                } else {
                    let i = choose |i: int| #![auto]
                        0 <= i < delta.entries@.len()
                        && delta.entries@[i].au as nat == au;
                    delta.entry_counts(i);
                }
            }
            assert(delta.removes() <= initial);
            assert forall |au: AU| #[trigger]
                target.count(au) <= u64::MAX as nat by {
                if forall |i: int| #![trigger delta.entries@[i]]
                    0 <= i < delta.entries@.len()
                    ==> delta.entries@[i].au as nat != au {
                    delta.target_count_without_entry(initial, au);
                } else {
                    let i = choose |i: int| #![auto]
                        0 <= i < delta.entries@.len()
                        && delta.entries@[i].au as nat == au;
                }
            }
            assert(delta.removes() == seq_to_au_likes(removes@));
            assert(delta.adds() == seq_to_au_likes(adds@));
            assert(au_likes_delta_applicable(initial, removes@, adds@));
        }

        index = 0;
        while index < delta.entries.len()
            invariant
                self.wf(),
                self.bucket_count == old(self).bucket_count,
                delta.wf(),
                index <= delta.entries.len(),
                forall |i: int| #![trigger delta.entries@[i]]
                    0 <= i < delta.entries@.len()
                    ==> initial.count(delta.entries@[i].au as nat)
                            >= delta.entries@[i].removes as nat
                        && target.count(delta.entries@[i].au as nat)
                            <= u64::MAX as nat,
                forall |au: AU| {
                    &&& (exists |i: int| #![auto]
                        0 <= i < index
                        && delta.entries@[i].au as nat == au)
                        ==> #[trigger] self@.count(au) == target.count(au)
                    &&& (forall |i: int| #![trigger delta.entries@[i]]
                        0 <= i < index
                        ==> delta.entries@[i].au as nat != au)
                        ==> #[trigger] self@.count(au) == initial.count(au)
                },
            decreases delta.entries.len() - index,
        {
            let entry = delta.entries[index];
            let remove_count = entry.removes as u64;
            let add_count = entry.adds as u64;
            let current = self.count(entry.au);
            proof {

                assert forall |i: int| #![trigger delta.entries@[i]]
                    0 <= i < index
                    implies delta.entries@[i].au != entry.au by {
                    assert(i != index);
                }
                assert(self@.count(entry.au as nat)
                    == initial.count(entry.au as nat));
                assert(current as nat == initial.count(entry.au as nat));
            }
            let after_removes = current - remove_count;
            proof {
                delta.target_count_for_entry(initial, index as int);
                assert(after_removes as nat + add_count as nat
                    == target.count(entry.au as nat));
                assert(after_removes as nat + add_count as nat
                    <= u64::MAX as nat);
            }
            let final_count = after_removes + add_count;
            let ghost before_update = self@;
            self.set_count(entry.au, final_count);
            proof {
                broadcast use vstd::multiset::group_multiset_properties;
                assert(final_count as nat == target.count(entry.au as nat));
                assert forall |au: AU| {
                    &&& (exists |i: int| #![auto]
                        0 <= i < index + 1
                        && delta.entries@[i].au as nat == au)
                        ==> #[trigger] self@.count(au) == target.count(au)
                    &&& (forall |i: int| #![trigger delta.entries@[i]]
                        0 <= i < index + 1
                        ==> delta.entries@[i].au as nat != au)
                        ==> #[trigger] self@.count(au) == initial.count(au)
                } by {
                    if au == entry.au as nat {
                        assert(self@.count(au) == final_count as nat);
                    } else {
                        assert(self@.count(au) == before_update.count(au));
                        if exists |i: int| #![auto]
                            0 <= i < index + 1
                            && delta.entries@[i].au as nat == au {
                            let i = choose |i: int| #![auto]
                                0 <= i < index + 1
                                && delta.entries@[i].au as nat == au;
                            assert(i < index);
                        }
                    }
                }
            }
            index += 1;
        }

        proof {
            assert(index == delta.entries@.len());
            assert_multisets_equal!(self@, target, au => {
                if exists |i: int| #![auto]
                    0 <= i < delta.entries@.len()
                    && delta.entries@[i].au as nat == au {
                    let i = choose |i: int| #![auto]
                        0 <= i < delta.entries@.len()
                        && delta.entries@[i].au as nat == au;
                    assert(i < index);
                } else {
                    delta.target_count_without_entry(initial, au);
                }
            });
            assert(delta.removes() == seq_to_au_likes(removes@));
            assert(delta.adds() == seq_to_au_likes(adds@));
            assert(target == initial.sub(seq_to_au_likes(removes@))
                .add(seq_to_au_likes(adds@)));
            assert(iau_seq_set(became_zero@) =~= initial.dom() - self@.dom());
        }
        AuLikesUpdateResult::Applied { became_zero }
    }

    pub fn increment(&mut self, au: IAU) -> (result: AuLikesUpdateResult)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            (result is Applied) <==>
                old(self)@.count(au as nat) < u64::MAX as nat,
            match result {
                AuLikesUpdateResult::Applied { became_zero } => {
                    &&& self@ == old(self)@.insert(au as nat)
                    &&& unique_iau_seq(became_zero@)
                    &&& iau_seq_set(became_zero@) =~=
                        old(self)@.dom() - self@.dom()
                },
                AuLikesUpdateResult::Noop => {
                    &&& self.buckets@ == old(self).buckets@
                    &&& self.bucket_count == old(self).bucket_count
                    &&& self@ == old(self)@
                },
            },
    {
        proof { self.view_counts_bounded(); }
        let removes = Vec::<IAU>::new();
        let mut adds = Vec::<IAU>::new();
        adds.push(au);
        let result = self.apply_delta(&removes, &adds);
        proof {
            assert(seq_to_au_likes(removes@) == AULikes::empty());
            assert(adds@ == seq![au]);
            broadcast use vstd::multiset::group_multiset_axioms;
            seq_to_au_likes_push(seq![], au);
            assert_multisets_equal!(
                AULikes::empty().insert(au as nat),
                AULikes::singleton(au as nat),
            );
            assert(seq_to_au_likes(adds@) == AULikes::singleton(au as nat));
            assert(old(self)@.sub(AULikes::empty()).add(AULikes::singleton(au as nat))
                == old(self)@.insert(au as nat));
            assert(au_likes_delta_applicable(old(self)@, removes@, adds@)
                <==> old(self)@.count(au as nat) < u64::MAX as nat) by {
                if au_likes_delta_applicable(old(self)@, removes@, adds@) {
                    assert(old(self)@.insert(au as nat).count(au as nat)
                        <= u64::MAX as nat);
                    assert(old(self)@.insert(au as nat).count(au as nat)
                        == old(self)@.count(au as nat) + 1);
                }
                assert forall |other: AU| #[trigger]
                    old(self)@.insert(au as nat).count(other) <= u64::MAX as nat
                    <==> (other != au as nat
                        || old(self)@.count(au as nat) < u64::MAX as nat) by {
                    if other != au as nat {
                        assert(old(self)@.insert(au as nat).count(other)
                            == old(self)@.count(other));
                    }
                }
            }
        }
        result
    }

    pub fn decrement(&mut self, au: IAU) -> (result: AuLikesUpdateResult)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.bucket_count == old(self).bucket_count,
            (result is Applied) <==> old(self)@.contains(au as nat),
            match result {
                AuLikesUpdateResult::Applied { became_zero } => {
                    &&& self@ == old(self)@.remove(au as nat)
                    &&& unique_iau_seq(became_zero@)
                    &&& iau_seq_set(became_zero@) =~=
                        old(self)@.dom() - self@.dom()
                },
                AuLikesUpdateResult::Noop => {
                    &&& self.buckets@ == old(self).buckets@
                    &&& self.bucket_count == old(self).bucket_count
                    &&& self@ == old(self)@
                },
            },
    {
        proof { self.view_counts_bounded(); }
        let mut removes = Vec::<IAU>::new();
        removes.push(au);
        let adds = Vec::<IAU>::new();
        let result = self.apply_delta(&removes, &adds);
        proof {
            assert(removes@ == seq![au]);
            assert(seq_to_au_likes(adds@) == AULikes::empty());
            broadcast use vstd::multiset::group_multiset_axioms;
            seq_to_au_likes_push(seq![], au);
            assert_multisets_equal!(
                AULikes::empty().insert(au as nat),
                AULikes::singleton(au as nat),
            );
            assert(seq_to_au_likes(removes@) == AULikes::singleton(au as nat));
            assert(old(self)@.sub(AULikes::singleton(au as nat)).add(AULikes::empty())
                == old(self)@.remove(au as nat));
            assert(au_likes_delta_applicable(old(self)@, removes@, adds@)
                <==> old(self)@.contains(au as nat)) by {
                assert(AULikes::singleton(au as nat) <= old(self)@
                    <==> old(self)@.contains(au as nat));
                assert forall |other: AU| #[trigger]
                    old(self)@.remove(au as nat).count(other) <= u64::MAX as nat by {
                    assert(old(self)@.remove(au as nat).count(other)
                        <= old(self)@.count(other));
                }
            }
        }
        result
    }
}

impl View for AuLikesImpl {
    type V = AULikes;

    open spec fn view(&self) -> AULikes {
        AULikes::from_map(Self::buckets_count_map(
            self.buckets@,
            self.bucket_count as nat,
        ))
    }
}

#[allow(dead_code)]
fn verify_au_likes_cases() {
    let mut likes = AuLikesImpl::new(2);

    let first = likes.increment(1);
    proof { assert(first is Applied); }
    let collision = likes.increment(3);
    proof { assert(collision is Applied); }
    let one_count = likes.count(1);
    let three_count = likes.count(3);
    proof {
        assert(one_count == 1);
        assert(three_count == 1);
    }

    let repeated = likes.increment(1);
    proof { assert(repeated is Applied); }
    let repeated_count = likes.count(1);
    proof { assert(repeated_count == 2); }

    let retained = likes.decrement(1);
    match retained {
        AuLikesUpdateResult::Applied { became_zero } => {
            proof {
                assert(likes@.count(1) == 1);
                assert(iau_seq_set(became_zero@) =~= Set::<AU>::empty());
            }
        },
        AuLikesUpdateResult::Noop => { proof { assert(false); } },
    }

    let reclaimed = likes.decrement(1);
    match reclaimed {
        AuLikesUpdateResult::Applied { became_zero } => {
            proof {
                assert(likes@.count(1) == 0);
                assert(unique_iau_seq(became_zero@));
                assert(iau_seq_set(became_zero@) =~= set![1nat]);
            }
        },
        AuLikesUpdateResult::Noop => { proof { assert(false); } },
    }

    let mut duplicate_adds = Vec::<IAU>::new();
    duplicate_adds.push(5);
    duplicate_adds.push(5);
    duplicate_adds.push(7);
    let no_removes = Vec::<IAU>::new();
    proof {
        likes.view_counts_bounded();
        broadcast use vstd::multiset::group_multiset_axioms;
        assert(duplicate_adds@ == seq![5u32, 5u32, 7u32]);
        assert(seq_to_au_likes(no_removes@) == AULikes::empty());
        seq_to_au_likes_push(seq![], 5u32);
        seq_to_au_likes_push(seq![5u32], 5u32);
        seq_to_au_likes_push(seq![5u32, 5u32], 7u32);
        seq_to_au_likes_push_count(seq![], 5u32, 5);
        seq_to_au_likes_push_count(seq![5u32], 5u32, 5);
        seq_to_au_likes_push_count(seq![5u32, 5u32], 7u32, 5);
        seq_to_au_likes_push_count(seq![], 5u32, 7);
        seq_to_au_likes_push_count(seq![5u32], 5u32, 7);
        seq_to_au_likes_push_count(seq![5u32, 5u32], 7u32, 7);
        assert(seq![].push(5u32) == seq![5u32]);
        assert(seq![5u32].push(5u32) == seq![5u32, 5u32]);
        assert(seq![5u32, 5u32].push(7u32) == seq![5u32, 5u32, 7u32]);
        assert(seq_to_au_likes(seq![5u32, 5u32, 7u32]).count(5) == 2);
        assert(seq_to_au_likes(seq![5u32, 5u32, 7u32]).count(7) == 1);
        assert(seq_to_au_likes(duplicate_adds@)
            == seq_to_au_likes(seq![5u32, 5u32, 7u32]));
        assert(seq_to_au_likes(duplicate_adds@).count(5) == 2);
        assert(seq_to_au_likes(duplicate_adds@).count(7) == 1);
        assert forall |au: AU| au != 5 && au != 7 implies
            #[trigger] seq_to_au_likes(duplicate_adds@).count(au) == 0 by {
            seq_to_au_likes_push_count(seq![], 5u32, au);
            seq_to_au_likes_push_count(seq![5u32], 5u32, au);
            seq_to_au_likes_push_count(seq![5u32, 5u32], 7u32, au);
            assert(seq_to_au_likes(seq![5u32, 5u32, 7u32]).count(au) == 0);
        }
        assert(likes@.count(5) == 0);
        assert(likes@.count(7) == 0);
        assert forall |au: AU| #[trigger]
            likes@.add(seq_to_au_likes(duplicate_adds@)).count(au)
                <= u64::MAX as nat by {
            if au == 5 || au == 7 {
            } else {
                assert(likes@.add(seq_to_au_likes(duplicate_adds@)).count(au)
                    == likes@.count(au));
            }
        }
        assert(au_likes_delta_applicable(
            likes@,
            no_removes@,
            duplicate_adds@,
        ));
    }
    let duplicate_result = likes.apply_delta(&no_removes, &duplicate_adds);
    proof { assert(duplicate_result is Applied); }
    let five_count = likes.count(5);
    let seven_count = likes.count(7);
    proof {
        assert(five_count == 2);
        assert(seven_count == 1);
    }

    let mut duplicate_removes = Vec::<IAU>::new();
    duplicate_removes.push(5);
    duplicate_removes.push(5);
    let mut readd = Vec::<IAU>::new();
    readd.push(5);
    proof {
        likes.view_counts_bounded();
        broadcast use vstd::multiset::group_multiset_axioms;
        assert(duplicate_removes@ == seq![5u32, 5u32]);
        assert(readd@ == seq![5u32]);
        seq_to_au_likes_push(seq![], 5u32);
        seq_to_au_likes_push(seq![5u32], 5u32);
        seq_to_au_likes_push_count(seq![], 5u32, 5);
        seq_to_au_likes_push_count(seq![5u32], 5u32, 5);
        let remove_likes = seq_to_au_likes(duplicate_removes@);
        let add_likes = seq_to_au_likes(readd@);
        assert(remove_likes.count(5) == 2);
        assert(add_likes.count(5) == 1);
        assert forall |au: AU| au != 5 implies
            #[trigger] remove_likes.count(au) == 0
            && #[trigger] add_likes.count(au) == 0 by {
            seq_to_au_likes_push_count(seq![], 5u32, au);
            seq_to_au_likes_push_count(seq![5u32], 5u32, au);
        }
        assert(remove_likes <= likes@) by {
            assert forall |au: AU| #[trigger]
                remove_likes.count(au) <= likes@.count(au) by { }
        }
        assert forall |au: AU| #[trigger]
            likes@.sub(remove_likes).add(add_likes).count(au)
                <= u64::MAX as nat by {
            if au == 5 {
                assert(likes@.sub(remove_likes).add(add_likes).count(au) == 1);
            } else {
                assert(likes@.sub(remove_likes).add(add_likes).count(au)
                    == likes@.count(au));
            }
        }
        assert(au_likes_delta_applicable(
            likes@,
            duplicate_removes@,
            readd@,
        ));
    }
    let readd_result = likes.apply_delta(&duplicate_removes, &readd);
    match readd_result {
        AuLikesUpdateResult::Applied { became_zero } => {
            proof {
                assert(likes@.count(5) == 1);
                assert(iau_seq_set(became_zero@) =~= Set::<AU>::empty());
            }
        },
        AuLikesUpdateResult::Noop => { proof { assert(false); } },
    }

    let empty_removes = Vec::<IAU>::new();
    let empty_adds = Vec::<IAU>::new();
    let ghost before_empty = likes@;
    let empty_result = likes.apply_delta(&empty_removes, &empty_adds);
    proof {
        assert(empty_result is Applied);
        assert(likes@ == before_empty);
    }

    let ghost before_underflow_buckets = likes.buckets@;
    let ghost before_underflow = likes@;
    proof { assert(!likes@.contains(99)); }
    let underflow = likes.decrement(99);
    proof {
        assert(underflow is Noop);
        assert(likes.buckets@ == before_underflow_buckets);
        assert(likes@ == before_underflow);
    }

    let mut overflow = AuLikesImpl::new(1);
    overflow.set_count(11, u64::MAX);
    proof {
        broadcast use vstd::multiset::group_multiset_properties;
        assert(overflow@.count(11) == u64::MAX as nat);
    }
    let max_count = overflow.count(11);
    let ghost before_overflow_buckets = overflow.buckets@;
    let ghost before_overflow = overflow@;
    proof {
        assert(max_count == u64::MAX);
        assert(overflow@.count(11) == u64::MAX as nat);
    }
    let overflow_result = overflow.increment(11);
    proof {
        assert(overflow_result is Noop);
        assert(overflow.buckets@ == before_overflow_buckets);
        assert(overflow@ == before_overflow);
    }
}

} // verus!
