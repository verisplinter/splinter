// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
// use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus! {

pub trait WF {
    open spec fn wf(&self) -> bool
    { true }
}

// I wanted to implement WF for every Integer, but Rust was all "I dunno, maybe
// some upstream crate is gonna implement Integer for Vec..." Sigh.
// impl<T: builtin::Integer> WF for T {
//     spec fn wf(&self) -> bool { true }
// }

impl WF for u8 { }
impl WF for u16 { }
impl WF for u32 { }
impl WF for u64 { }

impl<T: WF> WF for Vec<T> {
    open spec fn wf(&self) -> bool {
        forall |i| #![auto] 0<=i<self.len() ==> self[i].wf()
    }
}

impl<A: WF, B: WF> WF for (A,B) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf()
    }
}


} //verus!
