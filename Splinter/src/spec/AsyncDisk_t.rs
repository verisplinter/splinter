// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*};

use crate::spec::MapSpec_t::{ID};

verus!{

/// Address defined for spec code

/// The `AU` type is the type for a unique allocation unit identifier (thus we use `nat`s).
/// 
/// An Allocation Unit (AU) is the minimum disk unit the "external" (i.e.: top-level) allocator
/// allocates to data structures like the Betree and Journal. Allocation Units
/// are made up of contiguous disk sectors. AUs are specified as part of the
/// Splinter implementation. The goal of having large allocation blocks is to
/// amortize allocation costs efficiently for large amounts of data.
pub type AU = nat;

/// A page index within an AU (disk pages, so for SSDs these are on the order of 4KB).
pub type Page = nat;

/// An Address specifies a specific disk address (i.e.: an address that identifies a disk sector (or whatever
/// atomic addressing unit the disk in question uses)).
/// It does this by combining an AU index with a page index within the AU.
pub struct Address {
    /// The Allocation Unit index this address resides within.
    pub au: AU,
    /// Page index within AU for this address. In the range [0,page_count).
    pub page: Page,
}

/// Returns the number of a disk pages in an Allocation Unit. 
/// Left as an uninterpreted function since it's implementation defined.
pub closed spec(checked) fn page_count() -> nat;

/// Returns the number of Allocation Unit of the disk. 
/// Left as an uninterpreted function since it's implementation defined.
pub closed spec(checked) fn au_count() -> nat;

impl Address {
    /// Returns true iff this Address is well formed.
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.au < au_count()
        &&& self.page < page_count()
    }
}

/// models raw disk content
pub type RawPage = Seq<u8>;

// TODO: compute checksum
// pub open spec fn valid_checksum(raw_page: RawPage) -> bool
// {
//     true
// }

/// models the actual disk
pub type Disk = Map<Address, RawPage>;

// pub struct Disk{
//     pub content: Map<Address, RawPage>,
// }

pub enum GenericDiskRequest<A> {
    ReadReq{from: A},
    WriteReq{to: A, data: RawPage},
}

pub type DiskRequest = GenericDiskRequest<Address>;

impl DiskRequest {
    pub open spec fn addr(self) -> Address
    {
        match self {
            Self::ReadReq{from} => from,
            Self::WriteReq{to, data} => to,
        }   
    }
}

pub enum GenericDiskResponse {
    ReadResp{data: RawPage},
    WriteResp{},
}

pub type DiskResponse = GenericDiskResponse;

state_machine!{ AsyncDisk {
    fields {
        // ephemeral states
        pub requests: Map<ID, DiskRequest>,
        pub responses: Map<ID, DiskResponse>,

        // persistent disk content
        pub content: Disk,
    }

    pub enum Label {
        // models disk controller receiving & responding to disk ops
        DiskOps{requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>},  
        // models disk internal operation that actually read/write data
        Internal,
        // models the crash event
        Crash,
    }

    init!{ initialize() {
        init requests = Map::empty();
        init responses = Map::empty();
        init content = Map::empty();
    }}

    // no changes to the disk content
    transition!{ disk_ops(lbl: Label){
        require lbl is DiskOps;

        // disallow req & resp of the same request in an atomic step
        // => enforced via the trusted API
        // require lbl->requests.dom().disjoint(lbl->responses.dom());

        // new requests can't overlap with pending requests
        require lbl->requests.dom().disjoint(pre.requests.dom());
        // new requests can't overlap with pending responses
        require lbl->requests.dom().disjoint(pre.responses.dom());

        // responses heard must come from the pending response set
        require lbl->responses <= pre.responses;

        update requests = pre.requests.union_prefer_right(lbl->requests);
        update responses = pre.responses.remove_keys(lbl->responses.dom());
    }}

    // process reads
    transition!{ process_read(lbl: Label, id: ID){
        require lbl is Internal;

        // read processed must have been requested
        require pre.requests.dom().contains(id);
        require pre.requests[id] is ReadReq;
        require pre.requests[id]->from.wf();

        let read_resp = DiskResponse::ReadResp{
            data: pre.content[pre.requests[id]->from],
        };

        // require valid_checksum(read_resp->data);

        update requests = pre.requests.remove(id);
        update responses = pre.responses.insert(id, read_resp);
    }}

    // NOTE: we will skip modeling this for now
    // transition!{ process_read_failure(lbl: Label, id: ID, fake_content: RawPage){
    //     require lbl is Internal;

    //     // read processed must have been requested
    //     require pre.requests.dom().contains(id);
    //     require pre.requests[id] is ReadReq;
    //     require pre.requests[id]->from.wf();
        
    //     // restriction possible fake content
    //     require fake_content != pre.content[pre.requests[id]->from];
    //     // TODO: assume disk cannot fail from a checksum-correct state
    //     // to a different checksum-correct state (corrupted bits leads to mismatching checksums)
    //     require !valid_checksum(fake_content);

    //     let read_resp = DiskResponse::ReadResp{
    //         data: fake_content,
    //     };

    //     update requests = pre.requests.remove(id);
    //     update responses = pre.responses.insert(id, read_resp);
    // }}

    // process writes
    transition!{ process_write(lbl: Label, id: ID){
        require lbl is Internal;
    
        // write processed must have been requested
        require pre.requests.dom().contains(id);
        require pre.requests[id] is WriteReq;
        require pre.requests[id]->to.wf();

        // TODO: require write data matches its checksum

        let write_req = pre.requests[id];
        let write_resp = DiskResponse::WriteResp{};

        update requests = pre.requests.remove(id);
        update responses = pre.responses.insert(id, write_resp);
        update content = pre.content.insert(write_req->to, write_req->data);
    }}

    // forgets pending requests and replies, no change to disk content
    transition!{ crash(lbl: Label){
        require lbl is Crash;

        update requests = Map::empty();
        update responses = Map::empty();
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.requests.dom().disjoint(self.responses.dom())
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }
   
    #[inductive(disk_ops)]
    fn disk_ops_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(process_read)]
    fn process_read_inductive(pre: Self, post: Self, lbl: Label, id: ID) { }
   
    // #[inductive(process_read_failure)]
    // fn process_read_failure_inductive(pre: Self, post: Self, lbl: Label, id: ID, fake_content: RawPage) { }
   
    #[inductive(process_write)]
    fn process_write_inductive(pre: Self, post: Self, lbl: Label, id: ID) { }
   
    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) { }
}}

} // end of !verus
