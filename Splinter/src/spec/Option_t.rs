// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

pub enum Option<T> {
    None,
    Some(T),
}

} // verus!
