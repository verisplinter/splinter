// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;

use crate::spec::ImplDisk_t::{IAddress, IAU, IPage};
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;

verus! {

pub struct PageAllocator {
    au: IAU,
    next_page: IPage,
}

impl PageAllocator {
    pub closed spec fn wf(self) -> bool {
        true
    }

    pub closed spec fn alloc_au(self) -> IAU {
        self.au
    }

    pub closed spec fn alloc_au_nat(self) -> nat {
        self.au as nat
    }

    pub closed spec fn next_page(self) -> IPage {
        self.next_page
    }

    pub fn new(au: IAU, start_page: IPage) -> (out: Self)
        ensures
            out.wf(),
            out.alloc_au() == au,
            out.next_page() == start_page,
    {
        Self { au, next_page: start_page }
    }

    pub fn exec_alloc_au(&self) -> (out: IAU)
        ensures
            out == self.alloc_au(),
            out as nat == self.alloc_au_nat(),
    {
        self.au
    }

    pub fn peek_next_addr(&self) -> (out: IAddress)
        ensures
            out.au == self.alloc_au(),
            out.page == self.next_page(),
            out@.au == self.alloc_au_nat(),
    {
        IAddress { au: self.au, page: self.next_page }
    }

    pub fn advance_next_addr(&mut self)
        ensures
            self.wf(),
            self.alloc_au() == old(self).alloc_au(),
            self.next_page() == old(self).next_page() + 1,
    {
        if self.next_page == u32::MAX {
            convert_overflow_into_liveness_failure();
        }
        self.next_page = self.next_page + 1;
    }
}

} // verus!
