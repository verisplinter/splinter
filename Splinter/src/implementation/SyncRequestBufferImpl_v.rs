// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::spec::MapSpec_t::SyncReqId;

verus! {

pub struct SyncRequestBufferImpl {
    pub buffered_reqs: Vec<SyncReqId>,
    pub journal_cleaning_reqs: Vec<SyncReqId>,
    pub superblocking_reqs: Vec<SyncReqId>,
    pub sync_target_lsn: u64,
}

impl SyncRequestBufferImpl {
    fn vec_contains_id(ids: &Vec<SyncReqId>, id: SyncReqId) -> (out: bool)
        ensures out <==> ids@.contains(id),
    {
        let mut i = 0usize;
        while i < ids.len()
            invariant
                i <= ids.len(),
                forall |j: int| 0 <= j < i ==> ids@[j] != id,
            decreases ids.len() - i,
        {
            if ids[i] == id {
                return true;
            }
            i += 1;
        }
        false
    }

    pub fn contains_id(&self, id: SyncReqId) -> (out: bool)
        ensures out <==> self.all_ids().to_set().contains(id),
    {
        let in_cleaning = Self::vec_contains_id(&self.journal_cleaning_reqs, id);
        let in_superblocking = Self::vec_contains_id(&self.superblocking_reqs, id);
        let in_buffered = Self::vec_contains_id(&self.buffered_reqs, id);
        let out = in_cleaning || in_superblocking || in_buffered;
        proof {
            if out {
                if in_cleaning {
                    let i = choose |i: int| 0 <= i < self.journal_cleaning_reqs@.len()
                        && self.journal_cleaning_reqs@[i] == id;
                    assert(self.all_ids()[i] == id);
                } else if in_superblocking {
                    let i = choose |i: int| 0 <= i < self.superblocking_reqs@.len()
                        && self.superblocking_reqs@[i] == id;
                    let j = self.journal_cleaning_reqs@.len() as int + i;
                    assert(self.all_ids()[j] == id);
                } else {
                    let i = choose |i: int| 0 <= i < self.buffered_reqs@.len()
                        && self.buffered_reqs@[i] == id;
                    let j = self.journal_cleaning_reqs@.len() as int
                        + self.superblocking_reqs@.len() as int + i;
                    assert(self.all_ids()[j] == id);
                }
            }
        }
        out
    }

    pub open spec fn all_ids(&self) -> Seq<SyncReqId> {
        self.journal_cleaning_reqs@ + self.superblocking_reqs@ + self.buffered_reqs@
    }

    pub open spec fn ids_unique(&self) -> bool {
        forall |i: int, j: int| {
            &&& 0 <= i < self.all_ids().len()
            &&& 0 <= j < self.all_ids().len()
            &&& self.all_ids()[i] == self.all_ids()[j]
        } ==> i == j
    }

    pub fn new_empty() -> (out: Self)
        ensures
            out.all_ids() == Seq::<SyncReqId>::empty(),
            out.ids_unique(),
            out.sync_target_lsn == 0,
    {
        Self {
            buffered_reqs: Vec::new(),
            journal_cleaning_reqs: Vec::new(),
            superblocking_reqs: Vec::new(),
            sync_target_lsn: 0,
        }
    }

    pub fn promote_buffered(&mut self, target_lsn: u64)
        requires
            old(self).journal_cleaning_reqs@.len() == 0,
            old(self).superblocking_reqs@.len() == 0,
        ensures
            self.buffered_reqs@.len() == 0,
            self.journal_cleaning_reqs@ == old(self).buffered_reqs@,
            self.superblocking_reqs@.len() == 0,
            self.sync_target_lsn == target_lsn,
            self.all_ids() == old(self).all_ids(),
            old(self).ids_unique() ==> self.ids_unique(),
    {
        self.sync_target_lsn = target_lsn;
        core::mem::swap(&mut self.buffered_reqs, &mut self.journal_cleaning_reqs);
        proof {
            if old(self).ids_unique() {
                assert(self.ids_unique()) by {
                    assert forall |i: int, j: int| {
                        &&& 0 <= i < self.all_ids().len()
                        &&& 0 <= j < self.all_ids().len()
                        &&& self.all_ids()[i] == self.all_ids()[j]
                    } implies i == j by {
                        assert(self.all_ids() == old(self).all_ids());
                    }
                }
            }
        }
    }

    pub fn push_buffered(&mut self, id: SyncReqId)
        requires
            old(self).ids_unique(),
            !old(self).all_ids().to_set().contains(id),
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@.push(id),
            self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
            self.superblocking_reqs@ == old(self).superblocking_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            self.all_ids() == old(self).all_ids().push(id),
            self.all_ids().to_set() =~= old(self).all_ids().to_set().insert(id),
            self.ids_unique(),
    {
        self.buffered_reqs.push(id);
        proof {
            assert(self.all_ids() == old(self).all_ids().push(id));
            assert forall |x: SyncReqId| #[trigger] self.all_ids().to_set().contains(x)
                <==> old(self).all_ids().to_set().insert(id).contains(x) by {
                if self.all_ids().to_set().contains(x) {
                    let i = choose |i: int| 0 <= i < self.all_ids().len()
                        && self.all_ids()[i] == x;
                    if i < old(self).all_ids().len() {
                        assert(old(self).all_ids().to_set().contains(x));
                    } else {
                        assert(i == old(self).all_ids().len());
                        assert(x == id);
                    }
                } else if old(self).all_ids().to_set().insert(id).contains(x) {
                    if x == id {
                        assert(self.all_ids()[old(self).all_ids().len() as int] == id);
                    } else {
                        let i = choose |i: int| 0 <= i < old(self).all_ids().len()
                            && old(self).all_ids()[i] == x;
                        assert(self.all_ids()[i] == x);
                    }
                    assert(false);
                }
            }
            assert forall |i: int, j: int| {
                &&& 0 <= i < self.all_ids().len()
                &&& 0 <= j < self.all_ids().len()
                &&& self.all_ids()[i] == self.all_ids()[j]
            } implies i == j by {
                let old_len = old(self).all_ids().len();
                if i < old_len && j < old_len {
                    assert(i == j);
                } else if i == old_len && j == old_len {
                } else if i == old_len {
                    assert(old(self).all_ids()[j] == id);
                    assert(old(self).all_ids().to_set().contains(id));
                    assert(false);
                } else {
                    assert(old(self).all_ids()[i] == id);
                    assert(old(self).all_ids().to_set().contains(id));
                    assert(false);
                }
            }
        }
    }

    pub fn move_cleaning_to_superblocking(&mut self)
        requires old(self).superblocking_reqs@.len() == 0,
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@,
            self.journal_cleaning_reqs@.len() == 0,
            self.superblocking_reqs@ == old(self).journal_cleaning_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            self.all_ids() == old(self).all_ids(),
            old(self).ids_unique() ==> self.ids_unique(),
    {
        core::mem::swap(&mut self.journal_cleaning_reqs, &mut self.superblocking_reqs);
    }

    pub fn pop_superblocking(&mut self) -> (out: SyncReqId)
        requires
            old(self).superblocking_reqs@.len() > 0,
            old(self).ids_unique(),
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@,
            self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
            self.superblocking_reqs@.push(out) == old(self).superblocking_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            old(self).all_ids().to_set().contains(out),
            self.all_ids().to_set() =~= old(self).all_ids().to_set().remove(out),
            self.ids_unique(),
    {
        let out = self.superblocking_reqs.pop().unwrap();
        proof {
            let ghost old_ids = old(self).all_ids();
            let ghost new_ids = self.all_ids();
            let ghost old_super = old(self).superblocking_reqs@;
            let ghost new_super = self.superblocking_reqs@;
            assert(new_super.push(out) == old_super);
            let popped_idx = old(self).journal_cleaning_reqs@.len() as int
                + new_super.len() as int;
            assert(0 <= popped_idx < old_ids.len());
            assert(old_ids[popped_idx] == out);
            assert(old_ids.to_set().contains(out));

            assert forall |x: SyncReqId| #[trigger] new_ids.to_set().contains(x)
                implies old_ids.to_set().remove(out).contains(x) by {
                let i = choose |i: int| 0 <= i < new_ids.len() && new_ids[i] == x;
                if x == out {
                    if i < self.journal_cleaning_reqs@.len()
                        + self.superblocking_reqs@.len() {
                        assert(old_ids[i] == x);
                        assert(i != popped_idx);
                    } else {
                        let old_i = i + 1;
                        assert(old_ids[old_i] == x);
                        assert(old_i != popped_idx);
                    }
                    assert(false);
                }
                if i < self.journal_cleaning_reqs@.len()
                    + self.superblocking_reqs@.len() {
                    assert(old_ids[i] == x);
                } else {
                    assert(old_ids[i + 1] == x);
                }
            }
            assert forall |x: SyncReqId| #[trigger] old_ids.to_set().remove(out).contains(x)
                implies new_ids.to_set().contains(x) by {
                let i = choose |i: int| 0 <= i < old_ids.len() && old_ids[i] == x;
                assert(x != out);
                if i < old(self).journal_cleaning_reqs@.len() {
                    assert(new_ids[i] == x);
                } else if i < old(self).journal_cleaning_reqs@.len() + old_super.len() {
                    let super_i = i - old(self).journal_cleaning_reqs@.len();
                    if super_i == new_super.len() {
                        assert(old_ids[i] == out);
                        assert(false);
                    } else {
                        assert(new_ids[i] == x);
                    }
                } else {
                    assert(new_ids[i - 1] == x);
                }
            }
            assert forall |i: int, j: int| {
                &&& 0 <= i < new_ids.len()
                &&& 0 <= j < new_ids.len()
                &&& new_ids[i] == new_ids[j]
            } implies i == j by {
                let prefix_len = self.journal_cleaning_reqs@.len()
                    + self.superblocking_reqs@.len();
                let old_i = if i < prefix_len { i } else { i + 1 };
                let old_j = if j < prefix_len { j } else { j + 1 };
                assert(old_ids[old_i] == new_ids[i]);
                assert(old_ids[old_j] == new_ids[j]);
                assert(old_i == old_j);
                assert(i == j);
            }
        }
        out
    }
}

} // verus!
