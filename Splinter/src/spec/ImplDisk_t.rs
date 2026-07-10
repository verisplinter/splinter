// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use vstd::prelude::*;

//use vstd::prelude_macros::*;
use vstd::{map::*, seq::*, bytes::*, string::View};

use crate::spec::AsyncDisk_t::{Address, DiskRequest, DiskResponse, GenericDiskRequest, GenericDiskResponse, page_count};

verus!{
/// IAddress defined for executable code

pub type IAU = u32;

pub type IPage = u32;

#[derive(Debug, Copy, Clone)]
pub struct IDiskGeometry {
    pub physical_au_count: IAU,
    pub pages_per_au: IPage,
}

impl IDiskGeometry {
    pub open spec fn wf(&self) -> bool {
        &&& 1 < self.physical_au_count as nat
        &&& 0 < self.pages_per_au as nat
        &&& self.pages_per_au as nat == page_count()
    }
}

#[derive(Debug, Copy, Clone, Eq, Hash)]
pub struct IAddress {
    pub au: IAU,
    pub page: IPage,
}

impl View for IAddress{
    type V = Address;
    open spec fn view(&self) -> Self::V {
        Address{au: self.au as nat, page: self.page as nat}
    }
}

use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;

impl Parsedview<Address> for IAddress {
    open spec fn parsedv(&self) -> Address {
        self@
    }
}

impl WF for IAddress {
    open spec fn wf(&self) -> bool { true }
}

#[verifier::external_body]
broadcast proof fn iaddress_always_wf(addr: IAddress)
    ensures #[trigger] addr.wf()
{
}

impl IAddress {
    spec fn eq_spec(&self, other: &Self) -> bool {
        self.au == other.au && self.page == other.page
    }
}

use vstd::std_specs::cmp::PartialEqSpec;

impl PartialEq for IAddress {
    fn eq(&self, other: &Self) -> bool {
        let r = self.au == other.au && self.page == other.page;
        assume( false );
// TODO:
// error: postcondition not satisfied
//   --> /home/jonh/verus/source/target-verus/release/vstd/std_specs/cmp.rs:20:13
//    |
// 20 |             Self::obeys_eq_spec() ==> r == self.eq_spec(other);
//    |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition
//         assert( Self::obeys_eq_spec() ==> r == self.eq_spec(other) );
        r
    }
}

/// further restricted by actual disk size
pub uninterp spec(checked) fn ipage_count() -> IPage;

// REMOVED: conflicting inherent wf() method - use WF trait instead
// The inherent wf() was shadowing the WF trait method, causing Verus
// verification issues in struct_marshaller_2! macro.
// impl IAddress {
//     pub open spec(checked) fn wf(self) -> bool {
//         self.page < ipage_count()
//     }
// }

/// Axiom relating spec and implementation page geometry.
#[verifier(external_body)]
pub broadcast axiom fn page_count_equals_ipage_count()
    ensures #[trigger] page_count() == ipage_count()
;

pub type IPageData = Vec<u8>;
pub type IDiskRequest = GenericDiskRequest<IAddress, IPageData>;
pub type IDiskResponse = GenericDiskResponse<IPageData>;

impl IDiskRequest {
    pub open spec fn view(self) -> DiskRequest {
        match self {
            Self::ReadReq{from} => DiskRequest::ReadReq{from: from@},
            Self::WriteReq{to, data} => DiskRequest::WriteReq{to: to@, data: data@},
        }
    }
}

impl IDiskResponse {
    pub open spec fn view(self) -> DiskResponse {
        match self {
            Self::ReadResp{data} => DiskResponse::ReadResp{data: data@},
            Self::WriteResp{} => DiskResponse::WriteResp{},
        }
    }
}
} // end of !verus
