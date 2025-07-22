// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*, string::View};

use crate::spec::MapSpec_t::{ID};
use crate::spec::AsyncDisk_t::{*};

verus!{
/// IAddress defined for executable code

pub type IAU = u32;

pub type IPage = u32;

pub struct IAddress {
    pub au: IAU,
    pub page: IPage,
}

/// further restricted by actual disk size
pub uninterp spec(checked) fn ipage_count() -> IPage;

/// further restricted by actual disk size
pub uninterp spec(checked) fn iau_count() -> IAU;

impl IAddress {
    pub open spec fn view(self) -> Address {
        Address{au: self.au as nat, page: self.page as nat}
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.au < iau_count()
        &&& self.page < ipage_count()
    }
}

/// axioms relating spec and impl page and au count
#[verifier(external_body)]
pub broadcast axiom fn page_count_equals_ipage_count()
    ensures #[trigger] page_count() == ipage_count()
;

#[verifier(external_body)]
pub broadcast axiom fn au_count_equals_iau_count()
    ensures #[trigger] au_count() == iau_count()
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
