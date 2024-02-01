// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use crate::spec::KeyType_t::*;
use builtin_macros::*;
use vstd::set::*;

verus! {

#[is_variant]
pub enum Domain {
    EmptyDomain,
    Domain { start: Element, end: Element },
}

pub open spec(checked) fn total_domain() -> Domain {
    Domain::Domain { start: Element::min_elem(), end: Element::Max }
}

impl Domain {
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.is_Domain() ==> {
            &&& Element::lt(self.get_Domain_start(), self.get_Domain_end())
            &&& self.get_Domain_start().is_Elem()  // Note(Jialin): skipping elementIsKey since we are integrating element to contain key sized elements

        }
    }

    pub open spec(checked) fn contains(self, key: Key) -> bool {
        &&& self.is_Domain()
        &&& Element::lte(self.get_Domain_start(), to_element(key))
        &&& Element::lt(to_element(key), self.get_Domain_end())
    }

    pub open spec(checked) fn key_set(self) -> Set<Key> {
        Set::new(|k| self.contains(k))
    }
}

// end impl Domain

} // verus!
  // end verus!
