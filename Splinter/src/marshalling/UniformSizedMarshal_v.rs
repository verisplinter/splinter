// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformPairFormat_v::*;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;

verus! {

pub trait UniformSizedMarshal : Marshal + UniformSized {
    proof fn uniform_size_matches_spec_size(self: &Self)
    ensures forall |val: Self::DV| self.spec_size(val) == self.uniform_size()
    ;
}

}//verus!
