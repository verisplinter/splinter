// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;
use builtin_macros::*;

verus! {

// A marshalling Format *instance* is UniformSized if it always marshals to exactly the same number
// of bytes regardless of the value being marshalled.
//
// Note that these sizes are &self properties because there may be different
// instances of a UniformSized Format configured for different sizes, such
// as a 4-element-seq-of-u32 vs a 6-element-seq-of-32.

pub trait UniformSized {
    // "us_valid" to avoid tedious name collision with Marshal::valid,
    // even though they're assuredly the same concept. Maybe introduce
    // a Valid trait that they both "require"?
    spec fn us_valid(&self) -> bool
        ;

    spec fn uniform_size(&self) -> (sz: usize)
        ;

    proof fn uniform_size_ensures(&self)
    requires self.us_valid()
    ensures 0 < self.uniform_size()
    ;

    exec fn exec_uniform_size(&self) -> (sz: usize)
    requires self.us_valid()
    ensures sz == self.uniform_size()
    ;
}

}//verus!
