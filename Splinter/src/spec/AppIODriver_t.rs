// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use verus_builtin::*;

use verus_builtin_macros::*;
use verus_state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*};

use crate::spec::MapSpec_t::{ID};

verus!{

    pub trait AppIODriver {
        spec fn hello() -> bool;
        
        // must be able to translate some arbitrary system label into 
    }


}