// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};

verus! {

#[verifier::exec_allows_no_decreases_clause]
pub fn convert_overflow_into_liveness_failure()
    ensures false
{
    loop {}
}

} //verus!
