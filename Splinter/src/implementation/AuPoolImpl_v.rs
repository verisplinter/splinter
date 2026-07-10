// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::disk::GenericDisk_v::AU;
use crate::spec::ImplDisk_t::IAU;

verus! {

#[derive(Debug, Copy, Clone)]
pub struct AuRun {
    pub start: IAU,
    pub end: IAU,
}

impl AuRun {
    pub open spec fn wf(&self, total_aus: IAU) -> bool
    {
        &&& 0 < (self.start as nat)
        &&& (self.start as nat) <= (self.end as nat)
        &&& (self.end as nat) <= (total_aus as nat)
    }

    pub open spec fn nonempty(&self) -> bool
    {
        (self.start as nat) < (self.end as nat)
    }

    pub open spec fn len(&self) -> nat
        recommends
            (self.start as nat) <= (self.end as nat),
    {
        ((self.end as int) - (self.start as int)) as nat
    }

    pub open spec fn contains_au(&self, au: AU) -> bool
    {
        (self.start as nat) <= au && au < (self.end as nat)
    }

    pub open spec fn as_set(&self) -> Set<AU>
    {
        Set::new(|au: AU| self.contains_au(au))
    }
}

pub open spec fn initial_free_aus(total_aus: IAU) -> Set<AU>
{
    Set::new(|au: AU| 0 < au && au < (total_aus as nat))
}

pub open spec fn iau_vec_set(aus: Seq<IAU>) -> Set<AU>
{
    Set::new(|au: AU| exists |i: int| 0 <= i < aus.len() && #[trigger] (aus[i] as nat) == au)
}

pub struct AuAllocation {
    pub run: AuRun,
    pub aus: Vec<IAU>,
}

impl AuAllocation {
    pub open spec fn vec_matches_run(aus: Seq<IAU>, run: AuRun) -> bool
        recommends
            (run.start as nat) <= (run.end as nat),
    {
        &&& aus.len() == run.len()
        &&& forall |i: int| 0 <= i < aus.len() ==> {
            #[trigger] (aus[i] as nat) == (run.start as nat) + (i as nat)
        }
    }

    pub open spec fn wf(&self, total_aus: IAU) -> bool
    {
        &&& self.run.wf(total_aus)
        &&& self.run.nonempty()
        &&& Self::vec_matches_run(self.aus@, self.run)
    }

    pub open spec fn as_set(&self) -> Set<AU>
    {
        self.run.as_set()
    }

}

pub struct AuPoolImpl {
    pub runs: Vec<AuRun>,
}

impl View for AuPoolImpl {
    type V = Set<AU>;

    open spec fn view(&self) -> Self::V
    {
        self.as_set()
    }
}

impl AuPoolImpl {
    pub open spec fn runs_wf(runs: Seq<AuRun>, total_aus: IAU) -> bool
    {
        forall |i: int| 0 <= i < runs.len() ==> #[trigger] runs[i].wf(total_aus)
    }

    pub open spec fn runs_coalesced(runs: Seq<AuRun>) -> bool
    {
        forall |i: int| 0 <= i < runs.len() - 1 ==> {
            #[trigger] (runs[i].end as nat) < (runs[i + 1].start as nat)
        }
    }

    pub open spec fn runs_disjoint(runs: Seq<AuRun>) -> bool
    {
        forall |i: int, j: int, au: AU| #![trigger runs[i].contains_au(au), runs[j].contains_au(au)]
            0 <= i < runs.len() && 0 <= j < runs.len()
            && runs[i].contains_au(au) && runs[j].contains_au(au)
            ==> i == j
    }

    pub open spec fn runs_as_set(runs: Seq<AuRun>) -> Set<AU>
    {
        Set::new(|au: AU| exists |i: int|
            0 <= i < runs.len() && #[trigger] runs[i].contains_au(au))
    }

    pub open spec fn runs_all_before_run(runs: Seq<AuRun>, run: AuRun) -> bool
    {
        forall |i: int| 0 <= i < runs.len() ==> {
            #[trigger] (runs[i].end as nat) < (run.start as nat)
        }
    }

    pub open spec fn as_set(&self) -> Set<AU>
    {
        Self::runs_as_set(self.runs@)
    }

    pub open spec fn wf(&self, total_aus: IAU) -> bool
    {
        &&& 1 < (total_aus as nat)
        &&& Self::runs_wf(self.runs@, total_aus)
    }

    pub open spec fn canonical_wf(&self, total_aus: IAU) -> bool
    {
        &&& self.wf(total_aus)
        &&& Self::runs_coalesced(self.runs@)
        &&& Self::runs_disjoint(self.runs@)
    }

    pub proof fn runs_as_set_push(runs: Seq<AuRun>, run: AuRun)
        ensures
            Self::runs_as_set(runs.push(run)) =~= Self::runs_as_set(runs) + run.as_set(),
    {
        assert forall |au: AU| #[trigger] Self::runs_as_set(runs.push(run)).contains(au)
            implies (Self::runs_as_set(runs) + run.as_set()).contains(au) by {
            let i = choose |i: int| 0 <= i < runs.push(run).len()
                && #[trigger] runs.push(run)[i].contains_au(au);
            if i == runs.len() {
                assert(runs.push(run)[i] == run);
                assert(run.as_set().contains(au));
            } else {
                assert(runs.push(run)[i] == runs[i]);
                assert(Self::runs_as_set(runs).contains(au));
            }
        }
        assert forall |au: AU| #[trigger] (Self::runs_as_set(runs) + run.as_set()).contains(au)
            implies Self::runs_as_set(runs.push(run)).contains(au) by {
            if Self::runs_as_set(runs).contains(au) {
                let i = choose |i: int| 0 <= i < runs.len()
                    && #[trigger] runs[i].contains_au(au);
                assert(runs.push(run)[i] == runs[i]);
            } else {
                assert(run.as_set().contains(au));
                assert(runs.push(run)[runs.len() as int] == run);
            }
        }
    }

    pub proof fn runs_as_set_prefix_step(runs: Seq<AuRun>, idx: int)
        requires
            0 <= idx < runs.len(),
        ensures
            Self::runs_as_set(runs.subrange(0, idx + 1)) =~=
                Self::runs_as_set(runs.subrange(0, idx)) + runs[idx].as_set(),
    {
        assert(runs.subrange(0, idx + 1) == runs.subrange(0, idx).push(runs[idx]));
        Self::runs_as_set_push(runs.subrange(0, idx), runs[idx]);
    }

    pub proof fn push_run_preserves_canonical_parts(
        runs: Seq<AuRun>,
        run: AuRun,
        total_aus: IAU,
    )
        requires
            Self::runs_wf(runs, total_aus),
            Self::runs_coalesced(runs),
            Self::runs_disjoint(runs),
            Self::runs_all_before_run(runs, run),
            run.wf(total_aus),
        ensures
            Self::runs_wf(runs.push(run), total_aus),
            Self::runs_coalesced(runs.push(run)),
            Self::runs_disjoint(runs.push(run)),
    {
        assert forall |i: int| 0 <= i < runs.push(run).len()
            implies #[trigger] runs.push(run)[i].wf(total_aus) by {
            if i == runs.len() {
                assert(runs.push(run)[i] == run);
            } else {
                assert(runs.push(run)[i] == runs[i]);
                assert(runs[i].wf(total_aus));
            }
        }
        assert forall |i: int| 0 <= i < runs.push(run).len() - 1
            implies #[trigger] (runs.push(run)[i].end as nat)
                < (runs.push(run)[i + 1].start as nat) by {
            if i + 1 == runs.len() {
                assert(runs.push(run)[i] == runs[i]);
                assert(runs.push(run)[i + 1] == run);
                assert(Self::runs_all_before_run(runs, run));
            } else {
                assert(runs.push(run)[i] == runs[i]);
                assert(runs.push(run)[i + 1] == runs[i + 1]);
                assert(Self::runs_coalesced(runs));
            }
        }
        assert forall |i: int, j: int, au: AU|
            #![trigger runs.push(run)[i].contains_au(au), runs.push(run)[j].contains_au(au)]
            0 <= i < runs.push(run).len() && 0 <= j < runs.push(run).len()
            && runs.push(run)[i].contains_au(au) && runs.push(run)[j].contains_au(au)
            implies i == j by {
            if i == runs.len() {
                assert(runs.push(run)[i] == run);
                if j == runs.len() {
                } else {
                    assert(runs.push(run)[j] == runs[j]);
                    assert((runs[j].end as nat) < (run.start as nat));
                    assert(run.contains_au(au));
                    assert(runs[j].contains_au(au));
                    assert(false);
                }
            } else if j == runs.len() {
                assert(runs.push(run)[j] == run);
                assert(runs.push(run)[i] == runs[i]);
                assert((runs[i].end as nat) < (run.start as nat));
                assert(run.contains_au(au));
                assert(runs[i].contains_au(au));
                assert(false);
            } else {
                assert(runs.push(run)[i] == runs[i]);
                assert(runs.push(run)[j] == runs[j]);
                assert(Self::runs_disjoint(runs));
                assert(i == j);
            }
        }
    }

    pub proof fn runs_all_before_later(runs: Seq<AuRun>, current: AuRun, later: AuRun)
        requires
            Self::runs_all_before_run(runs, current),
            (current.start as nat) <= (current.end as nat),
            (current.end as nat) < (later.start as nat),
        ensures
            Self::runs_all_before_run(runs, later),
    {
        assert forall |i: int| 0 <= i < runs.len()
            implies #[trigger] (runs[i].end as nat) < (later.start as nat) by {
            assert((runs[i].end as nat) < (current.start as nat));
            assert((current.start as nat) <= (current.end as nat));
            assert((current.end as nat) < (later.start as nat));
        }
    }

    pub proof fn push_run_preserves_all_before(
        runs: Seq<AuRun>,
        pushed: AuRun,
        later: AuRun,
    )
        requires
            Self::runs_all_before_run(runs, later),
            (pushed.end as nat) < (later.start as nat),
        ensures
            Self::runs_all_before_run(runs.push(pushed), later),
    {
        assert forall |i: int| 0 <= i < runs.push(pushed).len()
            implies #[trigger] (runs.push(pushed)[i].end as nat) < (later.start as nat) by {
            if i == runs.len() {
                assert(runs.push(pushed)[i] == pushed);
            } else {
                assert(runs.push(pushed)[i] == runs[i]);
            }
        }
    }

    pub proof fn merged_run_union(before: AuRun, run: AuRun, merged: AuRun)
        requires
            !((run.end as nat) < (before.start as nat)),
            !((before.end as nat) < (run.start as nat)),
            merged.start == if run.start < before.start { run.start } else { before.start },
            merged.end == if before.end < run.end { run.end } else { before.end },
        ensures
            merged.as_set() =~= before.as_set() + run.as_set(),
    {
        assert forall |au: AU| #[trigger] merged.as_set().contains(au)
            <==> (before.as_set() + run.as_set()).contains(au) by {
        }
    }

    pub proof fn union_progress(
        old_left: Set<AU>,
        old_prefix: Set<AU>,
        item: Set<AU>,
        new_left: Set<AU>,
        new_prefix: Set<AU>,
        extra: Set<AU>,
    )
        requires
            old_left =~= old_prefix + extra,
            new_left =~= old_left + item,
            new_prefix =~= old_prefix + item,
        ensures
            new_left =~= new_prefix + extra,
    {
        assert forall |au: AU| #[trigger] new_left.contains(au)
            <==> (new_prefix + extra).contains(au) by {
        }
    }

    pub proof fn set_minus_singleton_union_step(prefix: Set<AU>, added: Set<AU>, removed: AU)
        ensures
            (prefix - set![removed]) + (added - set![removed]) =~=
                (prefix + added) - set![removed],
    {
        assert forall |au: AU| #[trigger] ((prefix - set![removed]) + (added - set![removed])).contains(au)
            <==> ((prefix + added) - set![removed]).contains(au) by {
        }
    }

    pub fn new(total_aus: IAU) -> (out: Self)
        requires
            1 < (total_aus as nat),
        ensures
            out.wf(total_aus),
            out.canonical_wf(total_aus),
            out@ =~= initial_free_aus(total_aus),
    {
        let mut runs = Vec::<AuRun>::new();
        runs.push(AuRun{start: 1, end: total_aus});
        let out = Self{runs};
        proof {
            assert(out.runs@.len() == 1);
            assert(out.runs@[0].wf(total_aus));
            assert(out.wf(total_aus));
            assert(out@ =~= initial_free_aus(total_aus)) by {
                assert forall |au: AU| #[trigger] out@.contains(au) implies initial_free_aus(total_aus).contains(au) by {
                    let i = choose |i: int| 0 <= i < out.runs@.len() && out.runs@[i].contains_au(au);
                    assert(i == 0);
                }
                assert forall |au: AU| #[trigger] initial_free_aus(total_aus).contains(au) implies out@.contains(au) by {
                    assert(out.runs@[0].contains_au(au));
                }
            }
        }
        out
    }

    pub fn run_to_vec(run: AuRun, total_aus: IAU) -> (out: Vec<IAU>)
        requires
            run.wf(total_aus),
        ensures
            AuAllocation::vec_matches_run(out@, run),
    {
        let mut out = Vec::<IAU>::new();
        let mut cur = run.start;
        while cur < run.end
            invariant
                run.wf(total_aus),
                (run.start as nat) <= (cur as nat) <= (run.end as nat),
                out@.len() == (cur as nat) - (run.start as nat),
                forall |i: int| 0 <= i < out@.len() ==> {
                    #[trigger] (out@[i] as nat) == (run.start as nat) + (i as nat)
                },
            decreases (run.end as nat) - (cur as nat)
        {
            out.push(cur);
            assert((cur as nat) + 1 <= (run.end as nat));
            cur = cur + 1;
        }
        out
    }

    pub fn alloc(&mut self, total_aus: IAU, count: IAU) -> (out: Option<AuAllocation>)
        requires
            old(self).canonical_wf(total_aus),
            0 < (count as nat),
        ensures
            self.canonical_wf(total_aus),
            match out {
                Some(alloc) => {
                    &&& alloc.wf(total_aus)
                    &&& alloc.as_set() <= old(self)@
                    &&& self@ =~= old(self)@ - alloc.as_set()
                },
                None => *self == *old(self),
            },
    {
        let mut idx: usize = 0;
        while idx < self.runs.len()
            invariant
                self.wf(total_aus),
                old(self).canonical_wf(total_aus) ==> self.canonical_wf(total_aus),
                0 <= idx <= self.runs.len(),
                *self == *old(self),
                self.runs@ == old(self).runs@,
            decreases self.runs.len() - idx
        {
            let run = self.runs[idx];
            proof {
                assert((idx as int) < self.runs@.len());
                assert(run == self.runs@[(idx as int)]);
                assert(Self::runs_wf(self.runs@, total_aus));
                assert(self.runs@[(idx as int)].wf(total_aus));
                assert((run.start as nat) <= (run.end as nat));
                assert(run.start <= run.end);
            }
            let available = run.end - run.start;
            if count <= available {
                proof {
                    assert((run.start as nat) + (count as nat) <= (run.end as nat));
                }
                let alloc_end = run.start + count;
                let alloc_run = AuRun{start: run.start, end: alloc_end};
                let updated_run = AuRun{start: alloc_end, end: run.end};

                proof {
                    assert((alloc_end as nat) == (run.start as nat) + (count as nat));
                    assert(0 < (run.start as nat));
                    assert((alloc_end as nat) <= (run.end as nat));
                    assert((run.end as nat) <= (total_aus as nat));
                    assert(alloc_run.wf(total_aus));
                    assert(alloc_run.nonempty());
                    assert(updated_run.wf(total_aus));
                }

                let ghost pre_runs = self.runs@;
                self.runs[idx] = updated_run;

                proof {
                    assert(self.runs@ == pre_runs.update((idx as int), updated_run));
                    assert(self.runs@[(idx as int)].wf(total_aus));
                    assert forall |i: int| 0 <= i < self.runs@.len()
                        implies #[trigger] self.runs@[i].wf(total_aus) by {
                        if i != (idx as int) {
                            assert(self.runs@[i] == pre_runs[i]);
                            assert(pre_runs[i].wf(total_aus));
                        }
                    }
                    assert(self.wf(total_aus));
                    if old(self).canonical_wf(total_aus) {
                        assert(Self::runs_coalesced(self.runs@)) by {
                            assert forall |i: int| 0 <= i < self.runs@.len() - 1
                                implies #[trigger] (self.runs@[i].end as nat) < (self.runs@[i + 1].start as nat) by {
                                assert(Self::runs_coalesced(pre_runs));
                                if i == (idx as int) {
                                    assert(self.runs@[i].end == pre_runs[i].end);
                                    assert(self.runs@[i + 1] == pre_runs[i + 1]);
                                } else if i + 1 == (idx as int) {
                                    assert(self.runs@[i] == pre_runs[i]);
                                    assert(self.runs@[i + 1].start == updated_run.start);
                                    assert((pre_runs[i + 1].start as nat) <= (updated_run.start as nat));
                                    assert((pre_runs[i].end as nat) < (pre_runs[i + 1].start as nat));
                                } else {
                                    assert(self.runs@[i] == pre_runs[i]);
                                    assert(self.runs@[i + 1] == pre_runs[i + 1]);
                                }
                            }
                        }
                        assert(Self::runs_disjoint(self.runs@)) by {
                            assert forall |i: int, j: int, au: AU| #![trigger self.runs@[i].contains_au(au), self.runs@[j].contains_au(au)]
                                0 <= i < self.runs@.len() && 0 <= j < self.runs@.len()
                                && self.runs@[i].contains_au(au)
                                && self.runs@[j].contains_au(au)
                                implies i == j by {
                                assert(Self::runs_disjoint(pre_runs));
                                if i == (idx as int) {
                                    assert(updated_run.contains_au(au));
                                    assert(pre_runs[i].contains_au(au));
                                    if j == (idx as int) {
                                        assert(i == j);
                                    } else {
                                        assert(self.runs@[j] == pre_runs[j]);
                                        assert(pre_runs[j].contains_au(au));
                                        assert(i == j);
                                    }
                                } else {
                                    assert(self.runs@[i] == pre_runs[i]);
                                    assert(pre_runs[i].contains_au(au));
                                    if j == (idx as int) {
                                        if self.runs@[j].contains_au(au) {
                                            assert(updated_run.contains_au(au));
                                            assert(pre_runs[j].contains_au(au));
                                            assert(i == j);
                                        }
                                    } else {
                                        assert(self.runs@[j] == pre_runs[j]);
                                        assert(pre_runs[j].contains_au(au));
                                        assert(i == j);
                                    }
                                }
                            }
                        }
                        assert(self.canonical_wf(total_aus));
                        assert(alloc_run.as_set() <= Self::runs_as_set(pre_runs)) by {
                            assert forall |au: AU| #[trigger] alloc_run.as_set().contains(au)
                                implies Self::runs_as_set(pre_runs).contains(au) by {
                                assert(alloc_run.contains_au(au));
                                assert(run.contains_au(au));
                                assert(pre_runs[(idx as int)].contains_au(au));
                            }
                        }
                        assert(Self::runs_as_set(self.runs@) =~= Self::runs_as_set(pre_runs) - alloc_run.as_set()) by {
                            assert forall |au: AU| #[trigger] Self::runs_as_set(self.runs@).contains(au)
                                implies (Self::runs_as_set(pre_runs) - alloc_run.as_set()).contains(au) by {
                                let post_i = choose |i: int| 0 <= i < self.runs@.len() && self.runs@[i].contains_au(au);
                                if post_i == (idx as int) {
                                    assert(updated_run.contains_au(au));
                                    assert(run.contains_au(au));
                                    assert(pre_runs[post_i].contains_au(au));
                                    assert(!alloc_run.contains_au(au));
                                } else {
                                    assert(self.runs@[post_i] == pre_runs[post_i]);
                                    assert(pre_runs[post_i].contains_au(au));
                                    if alloc_run.contains_au(au) {
                                        assert(pre_runs[(idx as int)].contains_au(au));
                                        assert(Self::runs_disjoint(pre_runs));
                                        assert(false);
                                    }
                                }
                            }
                            assert forall |au: AU| #[trigger] (Self::runs_as_set(pre_runs) - alloc_run.as_set()).contains(au)
                                implies Self::runs_as_set(self.runs@).contains(au) by {
                                let pre_i = choose |i: int| 0 <= i < pre_runs.len() && pre_runs[i].contains_au(au);
                                if pre_i == (idx as int) {
                                    assert(run.contains_au(au));
                                    assert(!alloc_run.contains_au(au));
                                    assert(updated_run.contains_au(au));
                                    assert(self.runs@[(idx as int)].contains_au(au));
                                } else {
                                    assert(self.runs@[pre_i] == pre_runs[pre_i]);
                                    assert(self.runs@[pre_i].contains_au(au));
                                }
                            }
                        }
                    }
                }

                let aus = Self::run_to_vec(alloc_run, total_aus);
                return Some(AuAllocation{run: alloc_run, aus});
            }
            idx = idx + 1;
        }
        proof {
            if old(self).canonical_wf(total_aus) {
                assert(self@ =~= old(self)@);
            }
        }
        None
    }

    pub fn free_run(&mut self, total_aus: IAU, returned: AuRun)
        requires
            old(self).canonical_wf(total_aus),
            returned.wf(total_aus),
            old(self)@.disjoint(returned.as_set()),
        ensures
            self.canonical_wf(total_aus),
            self@ =~= old(self)@ + returned.as_set(),
    {
        if returned.start == returned.end {
            return;
        }

        let mut merged = returned;
        let mut out = Vec::<AuRun>::new();
        let mut inserted = false;
        let mut idx: usize = 0;

        while idx < self.runs.len()
            invariant
                self.wf(total_aus),
                idx <= self.runs.len(),
                merged.wf(total_aus),
                returned.wf(total_aus),
                Self::runs_wf(out@, total_aus),
                Self::runs_coalesced(out@),
                Self::runs_disjoint(out@),
                !inserted ==> Self::runs_all_before_run(out@, merged),
                idx < self.runs.len() ==> Self::runs_all_before_run(out@, self.runs@[idx as int]),
                inserted && idx < self.runs.len()
                    ==> (merged.end as nat) < (self.runs@[idx as int].start as nat),
                !inserted ==> (Self::runs_as_set(out@) + merged.as_set()
                    =~= Self::runs_as_set(self.runs@.subrange(0, idx as int))
                        + returned.as_set()),
                inserted ==> (Self::runs_as_set(out@)
                    =~= Self::runs_as_set(self.runs@.subrange(0, idx as int))
                        + returned.as_set()),
            decreases self.runs.len() - idx
        {
            let run = self.runs[idx];
            let ghost idx_before = idx;
            let ghost merged_before = merged;
            let ghost out_before = out@;
            let ghost inserted_before = inserted;
            proof {
                assert((idx as int) < self.runs@.len());
                assert(run == self.runs@[(idx as int)]);
                assert(self.runs@[(idx as int)].wf(total_aus));
                assert(run.wf(total_aus));
            }

            if run.start == run.end {
                idx = idx + 1;
            } else if run.end < merged.start {
                let ghost pre_out = out@;
                out.push(run);
                proof {
                    Self::runs_as_set_push(pre_out, run);
                    assert(out@ == pre_out.push(run));
                    assert forall |i: int| 0 <= i < out@.len()
                        implies #[trigger] out@[i].wf(total_aus) by {
                        if i == pre_out.len() {
                            assert(out@[i] == run);
                        } else {
                            assert(out@[i] == pre_out[i]);
                            assert(pre_out[i].wf(total_aus));
                        }
                    }
                }
                idx = idx + 1;
            } else if merged.end < run.start {
                if !inserted {
                    let ghost pre_out = out@;
                    out.push(merged);
                    proof {
                        Self::runs_as_set_push(pre_out, merged);
                        assert(out@ == pre_out.push(merged));
                        assert forall |i: int| 0 <= i < out@.len()
                            implies #[trigger] out@[i].wf(total_aus) by {
                            if i == pre_out.len() {
                                assert(out@[i] == merged);
                            } else {
                                assert(out@[i] == pre_out[i]);
                                assert(pre_out[i].wf(total_aus));
                            }
                        }
                    }
                    inserted = true;
                }
                let ghost pre_out = out@;
                out.push(run);
                proof {
                    Self::runs_as_set_push(pre_out, run);
                    assert(out@ == pre_out.push(run));
                    assert forall |i: int| 0 <= i < out@.len()
                        implies #[trigger] out@[i].wf(total_aus) by {
                        if i == pre_out.len() {
                            assert(out@[i] == run);
                        } else {
                            assert(out@[i] == pre_out[i]);
                            assert(pre_out[i].wf(total_aus));
                        }
                    }
                }
                idx = idx + 1;
            } else {
                if run.start < merged.start {
                    merged.start = run.start;
                }
                if merged.end < run.end {
                    merged.end = run.end;
                }
                proof {
                    Self::merged_run_union(merged_before, run, merged);
                    assert(0 < (merged.start as nat));
                    assert((merged.start as nat) <= (merged.end as nat));
                    assert((merged.end as nat) <= (total_aus as nat));
                    assert(merged.wf(total_aus));
                }
                idx = idx + 1;
            }
            proof {
                Self::runs_as_set_prefix_step(self.runs@, idx_before as int);
                let old_prefix = Self::runs_as_set(
                    self.runs@.subrange(0, idx_before as int),
                );
                let new_prefix = Self::runs_as_set(
                    self.runs@.subrange(0, idx as int),
                );
                let old_left = if inserted_before {
                    Self::runs_as_set(out_before)
                } else {
                    Self::runs_as_set(out_before) + merged_before.as_set()
                };
                let new_left = if inserted {
                    Self::runs_as_set(out@)
                } else {
                    Self::runs_as_set(out@) + merged.as_set()
                };
                assert(old_left =~= old_prefix + returned.as_set());
                assert(new_prefix =~= old_prefix + run.as_set());
                assert(new_left =~= old_left + run.as_set()) by {
                    assert forall |au: AU| #[trigger] new_left.contains(au)
                        <==> (old_left + run.as_set()).contains(au) by {
                    }
                }
                Self::union_progress(
                    old_left,
                    old_prefix,
                    run.as_set(),
                    new_left,
                    new_prefix,
                    returned.as_set(),
                );
                if inserted {
                    assert(new_left == Self::runs_as_set(out@));
                } else {
                    assert(new_left == Self::runs_as_set(out@) + merged.as_set());
                }
            }
        }

        if !inserted {
            let ghost pre_out = out@;
            out.push(merged);
            proof {
                Self::runs_as_set_push(pre_out, merged);
                assert(out@ == pre_out.push(merged));
                assert forall |i: int| 0 <= i < out@.len()
                    implies #[trigger] out@[i].wf(total_aus) by {
                    if i == pre_out.len() {
                        assert(out@[i] == merged);
                    } else {
                        assert(out@[i] == pre_out[i]);
                        assert(pre_out[i].wf(total_aus));
                    }
                }
            }
        }
        proof {
            assert(Self::runs_as_set(out@) =~= old(self)@ + returned.as_set()) by {
                if inserted {
                    assert(Self::runs_as_set(out@)
                        =~= Self::runs_as_set(
                            self.runs@.subrange(0, self.runs@.len() as int),
                        ) + returned.as_set());
                } else {
                    assert(Self::runs_as_set(out@)
                        =~= Self::runs_as_set(
                            self.runs@.subrange(0, self.runs@.len() as int),
                        ) + returned.as_set());
                }
                assert(self.runs@.subrange(0, self.runs@.len() as int) == self.runs@);
            }
        }
        let ghost final_runs = out@;
        self.runs = out;
        proof {
            assert(self.runs@ == final_runs);
            assert(Self::runs_wf(self.runs@, total_aus));
            assert(self.wf(total_aus));
            assert(self@ =~= old(self)@ + returned.as_set());
        }
    }

    pub fn contains_au(&self, au: IAU) -> (out: bool)
        ensures
            out <==> self@.contains(au as nat),
    {
        let mut idx: usize = 0;
        while idx < self.runs.len()
            invariant
                idx <= self.runs.len(),
                forall |i: int| 0 <= i < idx
                    ==> !#[trigger] self.runs@[i].contains_au(au as nat),
            decreases self.runs.len() - idx,
        {
            let run = self.runs[idx];
            if run.start <= au && au < run.end {
                proof {
                    assert(run.contains_au(au as nat));
                    assert(self@.contains(au as nat));
                }
                return true;
            }
            idx = idx + 1;
        }
        false
    }

    pub fn free_aus(&mut self, total_aus: IAU, aus: &Vec<IAU>)
        requires
            old(self).canonical_wf(total_aus),
            forall |i: int| 0 <= i < aus@.len() ==> {
                &&& 0 < #[trigger] (aus@[i] as nat)
                &&& (aus@[i] as nat) < (total_aus as nat)
            },
            old(self)@.disjoint(iau_vec_set(aus@)),
        ensures
            self.canonical_wf(total_aus),
            self@ =~= old(self)@ + iau_vec_set(aus@),
    {
        let mut idx: usize = 0;
        while idx < aus.len()
            invariant
                idx <= aus.len(),
                self.canonical_wf(total_aus),
                forall |i: int| 0 <= i < aus@.len() ==> {
                    &&& 0 < #[trigger] (aus@[i] as nat)
                    &&& (aus@[i] as nat) < (total_aus as nat)
                },
                self@ =~= old(self)@ + iau_vec_set(aus@.subrange(0, idx as int)),
            decreases aus.len() - idx,
        {
            let au = aus[idx];
            if !self.contains_au(au) {
                let returned = AuRun{start: au, end: au + 1};
                proof {
                    assert(returned.wf(total_aus));
                    assert(returned.as_set() =~= set![au as nat]) by {
                        assert forall |x: AU| #[trigger] returned.as_set().contains(x)
                            <==> set![au as nat].contains(x) by {
                        }
                    }
                    assert(self@.disjoint(returned.as_set())) by {
                        assert(!self@.contains(au as nat));
                    }
                }
                self.free_run(total_aus, returned);
            }
            proof {
                assert(iau_vec_set(aus@.subrange(0, (idx + 1) as int))
                    =~= iau_vec_set(aus@.subrange(0, idx as int)) + set![au as nat]) by {
                    assert forall |x: AU| #[trigger]
                        iau_vec_set(aus@.subrange(0, (idx + 1) as int)).contains(x)
                        <==> (iau_vec_set(aus@.subrange(0, idx as int))
                            + set![au as nat]).contains(x) by {
                        if iau_vec_set(aus@.subrange(0, (idx + 1) as int)).contains(x) {
                            let i = choose |i: int|
                                0 <= i < aus@.subrange(0, (idx + 1) as int).len()
                                && #[trigger] (aus@.subrange(0, (idx + 1) as int)[i] as nat) == x;
                            if i < idx as int {
                                assert(aus@.subrange(0, (idx + 1) as int)[i]
                                    == aus@.subrange(0, idx as int)[i]);
                            } else {
                                assert(i == idx as int);
                                assert(aus@.subrange(0, (idx + 1) as int)[i] == au);
                            }
                        }
                        if (iau_vec_set(aus@.subrange(0, idx as int))
                            + set![au as nat]).contains(x) {
                            if iau_vec_set(aus@.subrange(0, idx as int)).contains(x) {
                                let i = choose |i: int|
                                    0 <= i < aus@.subrange(0, idx as int).len()
                                    && #[trigger] (aus@.subrange(0, idx as int)[i] as nat) == x;
                                assert(aus@.subrange(0, (idx + 1) as int)[i]
                                    == aus@.subrange(0, idx as int)[i]);
                            } else {
                                assert(x == au as nat);
                                assert(aus@.subrange(0, (idx + 1) as int)[idx as int] == au);
                            }
                        }
                    }
                }
                assert(self@ =~= old(self)@
                    + iau_vec_set(aus@.subrange(0, (idx + 1) as int))) by {
                    assert forall |x: AU| #[trigger] self@.contains(x)
                        <==> (old(self)@
                            + iau_vec_set(aus@.subrange(0, (idx + 1) as int))).contains(x) by {
                    }
                }
            }
            idx = idx + 1;
        }
        proof {
            assert(aus@.subrange(0, idx as int) == aus@);
        }
    }

    pub fn remove_au(&mut self, total_aus: IAU, au: IAU)
        requires
            old(self).canonical_wf(total_aus),
        ensures
            self.canonical_wf(total_aus),
            self@ =~= old(self)@ - set![au as nat],
    {
        let mut idx: usize = 0;
        let mut out = Vec::<AuRun>::new();
        while idx < self.runs.len()
            invariant
                self.runs@ == old(self).runs@,
                old(self).canonical_wf(total_aus),
                idx <= self.runs.len(),
                Self::runs_wf(out@, total_aus),
                Self::runs_coalesced(out@),
                Self::runs_disjoint(out@),
                idx < self.runs@.len() ==> Self::runs_all_before_run(out@, self.runs@[idx as int]),
                Self::runs_as_set(out@) =~=
                    Self::runs_as_set(self.runs@.subrange(0, idx as int)) - set![au as nat],
            decreases self.runs.len() - idx
        {
            let run = self.runs[idx];
            let ghost prefix = self.runs@.subrange(0, idx as int);
            let ghost out_at_start = out@;
            proof {
                assert((idx as int) < self.runs@.len());
                assert(run == self.runs@[idx as int]);
                assert(Self::runs_wf(self.runs@, total_aus));
                assert(run.wf(total_aus));
                if idx + 1 < self.runs.len() {
                    assert(Self::runs_coalesced(self.runs@));
                    assert((run.end as nat) < (self.runs@[(idx + 1) as int].start as nat));
                }
                Self::runs_as_set_prefix_step(self.runs@, idx as int);
            }
            if run.start <= au && au < run.end {
                let ghost mut added = Set::<AU>::empty();
                let ghost mut appended_set_ok = true;
                if run.start < au {
                    let left = AuRun{start: run.start, end: au};
                    proof {
                        assert((run.start as nat) < (au as nat));
                        assert((au as nat) < (run.end as nat));
                        assert(0 < (left.start as nat));
                        assert((left.start as nat) <= (left.end as nat));
                        assert((left.end as nat) <= (total_aus as nat));
                        assert(left.wf(total_aus));
                        assert(Self::runs_all_before_run(out@, left)) by {
                            assert forall |i: int| 0 <= i < out@.len()
                                implies #[trigger] (out@[i].end as nat) < (left.start as nat) by {
                                assert((out@[i].end as nat) < (run.start as nat));
                            }
                        }
                        Self::push_run_preserves_canonical_parts(out@, left, total_aus);
                    }
                    let ghost pre_out = out@;
                    out.push(left);
                    proof {
                        Self::runs_as_set_push(pre_out, left);
                        added = added + left.as_set();
                        assert(appended_set_ok);
                        assert(Self::runs_as_set(out@) =~= Self::runs_as_set(out_at_start) + added) by {
                            assert(Self::runs_as_set(pre_out) =~= Self::runs_as_set(out_at_start));
                        }
                    }
                }
                if au != u32::MAX {
                    let after = au + 1;
                    if after < run.end {
                        let right = AuRun{start: after, end: run.end};
                        proof {
                            assert((au as nat) + 1 == after as nat);
                            assert((after as nat) < (run.end as nat));
                            assert(0 < (right.start as nat));
                            assert((right.start as nat) <= (right.end as nat));
                            assert((right.end as nat) <= (total_aus as nat));
                            assert(right.wf(total_aus));
                            assert(Self::runs_all_before_run(out@, right)) by {
                                assert forall |i: int| 0 <= i < out@.len()
                                    implies #[trigger] (out@[i].end as nat) < (right.start as nat) by {
                                    if i < out_at_start.len() {
                                        assert((out@[i].end as nat) < (run.start as nat));
                                        assert((run.start as nat) <= (au as nat));
                                        assert((au as nat) < (after as nat));
                                    } else {
                                        assert(run.start < au);
                                        assert(out@[i].end as nat == au as nat);
                                        assert((au as nat) < (after as nat));
                                    }
                                }
                            }
                            Self::push_run_preserves_canonical_parts(out@, right, total_aus);
                        }
                        let ghost pre_out = out@;
                        out.push(right);
                        proof {
                            Self::runs_as_set_push(pre_out, right);
                            let ghost old_added = added;
                            added = added + right.as_set();
                            assert(Self::runs_as_set(out@) =~= Self::runs_as_set(out_at_start) + added) by {
                                assert(Self::runs_as_set(pre_out) =~= Self::runs_as_set(out_at_start) + old_added);
                            }
                        }
                    }
                }
                proof {
                    assert(added =~= run.as_set() - set![au as nat]) by {
                        assert forall |x: AU| #[trigger] added.contains(x)
                            implies (run.as_set() - set![au as nat]).contains(x) by {
                            if run.start < au && (AuRun{start: run.start, end: au}).as_set().contains(x) {
                                assert((run.start as nat) <= x);
                                assert(x < (au as nat));
                                assert(run.contains_au(x));
                                assert(x != au as nat);
                            } else {
                                assert(au != u32::MAX);
                                let after: IAU = (au + 1) as IAU;
                                assert(after < run.end);
                                assert(AuRun{start: after, end: run.end}.as_set().contains(x));
                                assert((after as nat) <= x);
                                assert((au as nat) < (after as nat));
                                assert(run.contains_au(x));
                                assert(x != au as nat);
                            }
                        }
                        assert forall |x: AU| #[trigger] (run.as_set() - set![au as nat]).contains(x)
                            implies added.contains(x) by {
                            assert(run.contains_au(x));
                            assert(x != au as nat);
                            if x < au as nat {
                                assert(run.start < au);
                                let left = AuRun{start: run.start, end: au};
                                assert(left.contains_au(x));
                                assert(left.as_set().contains(x));
                            } else {
                                assert((au as nat) < x);
                                assert(au != u32::MAX);
                                let after: IAU = (au + 1) as IAU;
                                assert((after as nat) <= x);
                                assert(after < run.end);
                                let right = AuRun{start: after, end: run.end};
                                assert(right.contains_au(x));
                                assert(right.as_set().contains(x));
                            }
                        }
                    }
                    assert(Self::runs_as_set(out@) =~=
                        Self::runs_as_set(out_at_start) + (run.as_set() - set![au as nat]));
                }
            } else {
                proof {
                    assert(Self::runs_all_before_run(out@, run));
                    Self::push_run_preserves_canonical_parts(out@, run, total_aus);
                }
                let ghost pre_out = out@;
                out.push(run);
                proof {
                    Self::runs_as_set_push(pre_out, run);
                    assert(!run.as_set().contains(au as nat)) by {
                        if run.as_set().contains(au as nat) {
                            assert(run.contains_au(au as nat));
                        }
                    }
                    assert(run.as_set() =~= run.as_set() - set![au as nat]) by {
                        assert forall |x: AU| #[trigger] run.as_set().contains(x)
                            <==> (run.as_set() - set![au as nat]).contains(x) by {
                            if x == au as nat {
                                assert(!run.as_set().contains(x));
                            }
                        }
                    }
                    assert(Self::runs_as_set(out@) =~=
                        Self::runs_as_set(out_at_start) + (run.as_set() - set![au as nat]));
                }
            }
            proof {
                Self::set_minus_singleton_union_step(
                    Self::runs_as_set(prefix),
                    run.as_set(),
                    au as nat,
                );
                assert(Self::runs_as_set(out@) =~=
                    Self::runs_as_set(self.runs@.subrange(0, (idx + 1) as int)) - set![au as nat]) by {
                    assert(Self::runs_as_set(self.runs@.subrange(0, (idx + 1) as int)) =~=
                        Self::runs_as_set(prefix) + run.as_set());
                }
                if idx + 1 < self.runs.len() {
                    let next = self.runs@[(idx + 1) as int];
                    Self::runs_all_before_later(out_at_start, run, next);
                    if run.start <= au && au < run.end {
                        assert(Self::runs_all_before_run(out@, next)) by {
                            assert forall |i: int| 0 <= i < out@.len()
                                implies #[trigger] (out@[i].end as nat) < (next.start as nat) by {
                                if i < out_at_start.len() {
                                    assert((out_at_start[i].end as nat) < (next.start as nat));
                                    if out@[i] != out_at_start[i] {
                                    }
                                } else {
                                    assert((out@[i].end as nat) <= (run.end as nat));
                                    assert((run.end as nat) < (next.start as nat));
                                }
                            }
                        }
                    } else {
                        Self::push_run_preserves_all_before(out_at_start, run, next);
                        assert(Self::runs_all_before_run(out@, next));
                    }
                }
            }
            idx = idx + 1;
        }
        let ghost final_runs = out@;
        self.runs = out;
        proof {
            assert(self.runs@ == final_runs);
            assert(old(self).runs@.subrange(0, old(self).runs@.len() as int) == old(self).runs@);
            assert(Self::runs_wf(self.runs@, total_aus));
            assert(Self::runs_coalesced(self.runs@));
            assert(Self::runs_disjoint(self.runs@));
            assert(self.wf(total_aus));
            assert(self.canonical_wf(total_aus));
            assert(self@ =~= old(self)@ - set![au as nat]) by {
                assert(Self::runs_as_set(self.runs@) =~=
                    Self::runs_as_set(old(self).runs@) - set![au as nat]);
            }
        }
    }

    pub fn remove_aus(&mut self, total_aus: IAU, aus: Vec<IAU>)
        requires
            old(self).canonical_wf(total_aus),
        ensures
            self.canonical_wf(total_aus),
            self@ =~= old(self)@ - iau_vec_set(aus@),
    {
        let mut au_idx: usize = 0;
        while au_idx < aus.len()
            invariant
                au_idx <= aus.len(),
                self.canonical_wf(total_aus),
                self@ =~= old(self)@ - iau_vec_set(aus@.subrange(0, au_idx as int)),
            decreases aus.len() - au_idx
        {
            let au = aus[au_idx];
            self.remove_au(total_aus, au);
            proof {
                assert(iau_vec_set(aus@.subrange(0, (au_idx + 1) as int)) =~=
                    iau_vec_set(aus@.subrange(0, au_idx as int)) + set![au as nat]) by {
                    assert forall |x: AU| #[trigger] iau_vec_set(aus@.subrange(0, (au_idx + 1) as int)).contains(x)
                        <==> (iau_vec_set(aus@.subrange(0, au_idx as int)) + set![au as nat]).contains(x) by {
                        if iau_vec_set(aus@.subrange(0, (au_idx + 1) as int)).contains(x) {
                            let i = choose |i: int| 0 <= i < aus@.subrange(0, (au_idx + 1) as int).len()
                                && #[trigger] (aus@.subrange(0, (au_idx + 1) as int)[i] as nat) == x;
                            if i < au_idx as int {
                                assert(aus@.subrange(0, (au_idx + 1) as int)[i] == aus@.subrange(0, au_idx as int)[i]);
                            } else {
                                assert(i == au_idx as int);
                                assert(aus@.subrange(0, (au_idx + 1) as int)[i] == au);
                            }
                        }
                        if (iau_vec_set(aus@.subrange(0, au_idx as int)) + set![au as nat]).contains(x) {
                            if iau_vec_set(aus@.subrange(0, au_idx as int)).contains(x) {
                                let i = choose |i: int| 0 <= i < aus@.subrange(0, au_idx as int).len()
                                    && #[trigger] (aus@.subrange(0, au_idx as int)[i] as nat) == x;
                                assert(aus@.subrange(0, (au_idx + 1) as int)[i] == aus@.subrange(0, au_idx as int)[i]);
                            } else {
                                assert(x == au as nat);
                                assert(aus@.subrange(0, (au_idx + 1) as int)[au_idx as int] == au);
                            }
                        }
                    }
                }
                assert(self@ =~= old(self)@ - iau_vec_set(aus@.subrange(0, (au_idx + 1) as int))) by {
                    assert forall |x: AU| #[trigger] self@.contains(x)
                        <==> (old(self)@ - iau_vec_set(aus@.subrange(0, (au_idx + 1) as int))).contains(x) by {
                    }
                }
            }
            au_idx = au_idx + 1;
        }
        proof {
            assert(aus@.subrange(0, au_idx as int) == aus@);
        }
    }
}

} // verus!
