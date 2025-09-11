// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]

use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub trait Injective {
    proof fn lemma_injective()
        where Self: View + Sized
    ensures forall |x1: Self, x2: Self| x1@ == x2@ ==> x1 == x2
    ;
}

} // verus!
