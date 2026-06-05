// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

verus! {

pub enum RecoveryState {
    // Haven't done anything; don't know anything. Better not handle user IO.
    Begin,
    // We've sent the superblock read request; better not send any more. Still can't do user IO.
    AwaitingSuperblock,
    // The superblock has been read, so journal pages can be loaded into cache.
    SuperblockAvailable,
    // Journal and branch metadata are loaded; recovery can replay journal records.
    MetadataLoadComplete,
    // System can now operate.
    RecoveryComplete,
}

} // verus!
