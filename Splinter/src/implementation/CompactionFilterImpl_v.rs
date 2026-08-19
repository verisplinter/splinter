// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_seqs_equal};

use crate::betree::LinkedBetree_v::BetreeNode;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::spec::KeyType_t::{Element, Key, to_element};
use crate::implementation::BetreeQueryImpl_v::betree_route_index;
use crate::implementation::IBetreeNode_v::{IBetreeNode, IElement};

verus! {

pub struct CompactionFilterImpl {
    pub pivots: Vec<IElement>,
    pub flushed: Vec<u64>,
    pub buffer_count: usize,
    pub start: usize,
    pub end: usize,
    pub target: Ghost<BetreeNode>,
}

pub enum CompactionLiveStart {
    Live { input_idx: usize },
    Filtered,
}

fn clone_filter_pivots(pivots: &Vec<IElement>) -> (out: Vec<IElement>)
    ensures
        Parsedview::<Seq<Element>>::parsedv(&out)
            == Parsedview::<Seq<Element>>::parsedv(pivots),
{
    let mut out = Vec::<IElement>::new();
    let mut idx = 0usize;
    while idx < pivots.len()
        invariant
            idx <= pivots.len(),
            Parsedview::<Seq<Element>>::parsedv(&out)
                == Parsedview::<Seq<Element>>::parsedv(pivots)
                    .take(idx as int),
        decreases pivots.len() - idx,
    {
        out.push(pivots[idx].clone_checked());
        idx += 1;
    }
    proof {
        assert(Parsedview::<Seq<Element>>::parsedv(pivots)
            .take(idx as int)
            == Parsedview::<Seq<Element>>::parsedv(pivots));
    }
    out
}

fn clone_filter_offsets(offsets: &Vec<u64>) -> (out: Vec<u64>)
    ensures out@ == offsets@,
{
    let mut out = Vec::<u64>::new();
    let mut idx = 0usize;
    while idx < offsets.len()
        invariant
            idx <= offsets.len(),
            out@ == offsets@.take(idx as int),
        decreases offsets.len() - idx,
    {
        out.push(offsets[idx]);
        idx += 1;
    }
    proof {
        assert(offsets@.take(idx as int) == offsets@);
    }
    out
}

fn element_lte_key(element: &IElement, key: Key) -> (out: bool)
    ensures out == Element::lte(element@, to_element(key)),
{
    match element {
        IElement::Max => false,
        IElement::Elem { e } => *e <= key.0,
    }
}

fn key_lt_element(key: Key, element: &IElement) -> (out: bool)
    ensures out == Element::lt(to_element(key), element@),
{
    match element {
        IElement::Max => true,
        IElement::Elem { e } => key.0 < *e,
    }
}

fn ielement_equal(left: &IElement, right: &IElement) -> (out: bool)
    ensures out == (left@ == right@),
{
    match (left, right) {
        (IElement::Max, IElement::Max) => true,
        (IElement::Elem { e: left_e }, IElement::Elem { e: right_e }) => {
            *left_e == *right_e
        },
        _ => false,
    }
}

fn filter_pivots_equal(
    left: &Vec<IElement>,
    right: &Vec<IElement>,
) -> (out: bool)
    ensures
        out == (Parsedview::<Seq<Element>>::parsedv(left)
            == Parsedview::<Seq<Element>>::parsedv(right)),
{
    if left.len() != right.len() {
        proof {
            assert(Parsedview::<Seq<Element>>::parsedv(left).len()
                != Parsedview::<Seq<Element>>::parsedv(right).len());
        }
        return false;
    }
    let mut idx = 0usize;
    while idx < left.len()
        invariant
            left.len() == right.len(),
            idx <= left.len(),
            forall |i: int| 0 <= i < idx
                ==> (#[trigger] left@[i])@ == right@[i]@,
        decreases left.len() - idx,
    {
        if !ielement_equal(&left[idx], &right[idx]) {
            proof {
                assert(Parsedview::<Seq<Element>>::parsedv(left)[idx as int]
                    != Parsedview::<Seq<Element>>::parsedv(right)[idx as int]);
            }
            return false;
        }
        idx += 1;
    }
    proof {
        assert_seqs_equal!(
            Parsedview::<Seq<Element>>::parsedv(left),
            Parsedview::<Seq<Element>>::parsedv(right),
            i => {}
        );
    }
    true
}

fn filter_offsets_equal(left: &Vec<u64>, right: &Vec<u64>) -> (out: bool)
    ensures
        out == (Parsedview::<Seq<nat>>::parsedv(left)
            == Parsedview::<Seq<nat>>::parsedv(right)),
{
    if left.len() != right.len() {
        proof {
            assert(Parsedview::<Seq<nat>>::parsedv(left).len()
                != Parsedview::<Seq<nat>>::parsedv(right).len());
        }
        return false;
    }
    let mut idx = 0usize;
    while idx < left.len()
        invariant
            left.len() == right.len(),
            idx <= left.len(),
            forall |i: int| 0 <= i < idx
                ==> #[trigger] left@[i] == right@[i],
        decreases left.len() - idx,
    {
        if left[idx] != right[idx] {
            proof {
                assert(Parsedview::<Seq<nat>>::parsedv(left)[idx as int]
                    != Parsedview::<Seq<nat>>::parsedv(right)[idx as int]);
            }
            return false;
        }
        idx += 1;
    }
    proof {
        assert_seqs_equal!(
            Parsedview::<Seq<nat>>::parsedv(left),
            Parsedview::<Seq<nat>>::parsedv(right),
            i => {}
        );
    }
    true
}

impl CompactionFilterImpl {
    pub open spec fn wf(&self) -> bool {
        &&& self.target@.wf()
        &&& 0 <= self.start < self.end
            <= self.target@.buffers.len()
        &&& Parsedview::<Seq<Element>>::parsedv(&self.pivots)
            == self.target@.pivots.pivots
        &&& Parsedview::<Seq<nat>>::parsedv(&self.flushed)
            == self.target@.flushed.offsets
        &&& self.buffer_count == self.target@.buffers.len()
    }

    pub fn from_target(
        target: &IBetreeNode,
        start: usize,
        end: usize,
    ) -> (out: Self)
        requires
            target.wf(),
            target@.wf(),
            start < end <= target.buffers.len(),
        ensures
            out.wf(),
            out.target@ == target@,
            out.start == start,
            out.end == end,
    {
        let pivots = clone_filter_pivots(&target.pivots);
        let flushed = target.flushed.clone();
        let out = Self {
            pivots,
            flushed,
            buffer_count: target.buffers.len(),
            start,
            end,
            target: Ghost(target@),
        };
        proof {
            assert(target.buffers@.len() == target.buffers.len());
            assert(out.wf());
        }
        out
    }

    pub fn clone_checked(&self) -> (out: Self)
        requires self.wf(),
        ensures
            out.wf(),
            out.target@ == self.target@,
            out.start == self.start,
            out.end == self.end,
            out.buffer_count == self.buffer_count,
            Parsedview::<Seq<Element>>::parsedv(&out.pivots)
                == Parsedview::<Seq<Element>>::parsedv(&self.pivots),
            Parsedview::<Seq<nat>>::parsedv(&out.flushed)
                == Parsedview::<Seq<nat>>::parsedv(&self.flushed),
    {
        let out = Self {
            pivots: clone_filter_pivots(&self.pivots),
            flushed: clone_filter_offsets(&self.flushed),
            buffer_count: self.buffer_count,
            start: self.start,
            end: self.end,
            target: self.target,
        };
        proof {
            assert(out.wf());
        }
        out
    }

    pub fn matches_target_metadata(
        &self,
        target: &IBetreeNode,
    ) -> (out: bool)
        requires
            self.wf(),
            target.wf(),
            target@.wf(),
        ensures
            out == ({
                &&& self.target@.pivots.pivots
                    == target@.pivots.pivots
                &&& self.target@.flushed.offsets
                    == target@.flushed.offsets
                &&& self.target@.buffers.len()
                    == target@.buffers.len()
            }),
            out ==> self.target@.make_offset_map()
                == target@.make_offset_map(),
    {
        let pivots_equal = filter_pivots_equal(
            &self.pivots,
            &target.pivots,
        );
        let offsets_equal = filter_offsets_equal(
            &self.flushed,
            &target.flushed,
        );
        let buffer_counts_equal = self.buffer_count == target.buffers.len();
        proof {
            assert(Parsedview::<Seq<Element>>::parsedv(&self.pivots)
                == self.target@.pivots.pivots);
            assert(Parsedview::<Seq<Element>>::parsedv(&target.pivots)
                == target@.pivots.pivots);
            assert(Parsedview::<Seq<nat>>::parsedv(&self.flushed)
                == self.target@.flushed.offsets);
            assert(Parsedview::<Seq<nat>>::parsedv(&target.flushed)
                == target@.flushed.offsets);
            assert(pivots_equal == (self.target@.pivots.pivots
                == target@.pivots.pivots));
            assert(offsets_equal == (self.target@.flushed.offsets
                == target@.flushed.offsets));
            assert(buffer_counts_equal == (self.target@.buffers.len()
                == target@.buffers.len()));
            if pivots_equal && offsets_equal && buffer_counts_equal {
                assert forall |key: Key|
                    self.target@.key_in_domain(key)
                        == target@.key_in_domain(key) by {
                }
                assert_maps_equal!(
                    self.target@.make_offset_map().offsets,
                    target@.make_offset_map().offsets,
                    key => {
                        if self.target@.key_in_domain(key) {
                            assert(self.target@.pivots.route(key)
                                == target@.pivots.route(key));
                            assert(self.target@.flushed_ofs(key)
                                == target@.flushed_ofs(key));
                        }
                    }
                );
            }
        }
        pivots_equal && offsets_equal && buffer_counts_equal
    }

    pub fn key_in_domain(
        &self,
        key: Key,
    ) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self.target@.key_in_domain(key),
    {
        let lower = element_lte_key(&self.pivots[0], key);
        let upper = key_lt_element(
            key,
            &self.pivots[self.pivots.len() - 1],
        );
        proof {
            assert(self.pivots.len() == self.target@.pivots.pivots.len());
            assert(self.pivots.len() > 1);
            assert(self.pivots[0]@ == self.target@.pivots.pivots[0]);
            assert(self.pivots[(self.pivots.len() - 1) as int]@
                == self.target@.pivots.pivots.last());
        }
        lower && upper
    }

    pub fn live_start(
        &self,
        key: Key,
    ) -> (out: CompactionLiveStart)
        requires
            self.wf(),
        ensures
            match out {
                CompactionLiveStart::Live { input_idx } => {
                    &&& self.target@.key_in_domain(key)
                    &&& self.target@.flushed_ofs(key) <= self.end as nat
                    &&& input_idx as nat == if self.target@.flushed_ofs(key)
                        <= self.start as nat {
                        0
                    } else {
                        (self.target@.flushed_ofs(key) - self.start as nat) as nat
                    }
                    &&& input_idx as nat
                        == self.target@.make_offset_map().decrement(
                            self.start as nat,
                        ).offsets[key]
                },
                CompactionLiveStart::Filtered => {
                    !self.target@.key_in_domain(key)
                        || (self.end as nat) < self.target@.flushed_ofs(key)
                },
            },
    {
        if !self.key_in_domain(key) {
            return CompactionLiveStart::Filtered;
        }
        proof {
            Element::strictly_sorted_implies_sorted(
                self.target@.pivots.pivots,
            );
        }
        let route = betree_route_index(&self.pivots, key);
        proof {
            assert(route as int == self.target@.pivots.route(key));
            self.target@.pivots.route_lemma(key);
            assert((route as int) < self.target@.children.len());
            assert(self.target@.children.len()
                == self.target@.flushed.offsets.len());
            assert(self.flushed.len()
                == self.target@.flushed.offsets.len());
            assert(route < self.flushed.len());
            assert(self.flushed@[route as int] as nat
                == self.target@.flushed.offsets[route as int]);
            assert(self.target@.flushed_ofs(key)
                == self.flushed@[route as int] as nat);
        }
        let flushed = self.flushed[route];
        if flushed as u128 > self.end as u128 {
            proof {
                assert((self.end as nat) < (flushed as nat));
            }
            return CompactionLiveStart::Filtered;
        }
        let input_idx = if flushed as u128 <= self.start as u128 {
            0usize
        } else {
            flushed as usize - self.start
        };
        proof {
            assert(input_idx as nat == if self.target@.flushed_ofs(key)
                <= self.start as nat {
                0
            } else {
                (self.target@.flushed_ofs(key) - self.start as nat) as nat
            });
            assert(self.target@.make_offset_map().offsets[key]
                == self.target@.flushed_ofs(key));
            assert(self.target@.make_offset_map().decrement(
                self.start as nat,
            ).offsets[key] == input_idx as nat);
        }
        CompactionLiveStart::Live { input_idx }
    }
}

}
