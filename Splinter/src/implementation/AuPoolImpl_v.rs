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
            old(self).wf(total_aus),
            0 < (count as nat),
        ensures
            self.wf(total_aus),
            old(self).canonical_wf(total_aus) ==> self.canonical_wf(total_aus),
            match out {
                Some(alloc) => alloc.wf(total_aus),
                None => true,
            },
            old(self).canonical_wf(total_aus) ==> match out {
                Some(alloc) => {
                    &&& alloc.as_set() <= old(self)@
                    &&& self@ =~= old(self)@ - alloc.as_set()
                },
                None => self@ =~= old(self)@,
            },
    {
        let mut idx: usize = 0;
        while idx < self.runs.len()
            invariant
                self.wf(total_aus),
                old(self).canonical_wf(total_aus) ==> self.canonical_wf(total_aus),
                0 <= idx <= self.runs.len(),
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
            old(self).wf(total_aus),
            returned.wf(total_aus),
        ensures
            self.wf(total_aus),
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
            decreases self.runs.len() - idx
        {
            let run = self.runs[idx];
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
                    assert(0 < (merged.start as nat));
                    assert((merged.start as nat) <= (merged.end as nat));
                    assert((merged.end as nat) <= (total_aus as nat));
                    assert(merged.wf(total_aus));
                }
                idx = idx + 1;
            }
        }

        if !inserted {
            let ghost pre_out = out@;
            out.push(merged);
            proof {
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
        let ghost final_runs = out@;
        self.runs = out;
        proof {
            assert(self.runs@ == final_runs);
            assert(Self::runs_wf(self.runs@, total_aus));
            assert(self.wf(total_aus));
        }
    }
}

} // verus!
