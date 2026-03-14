// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use vstd::prelude::*;

// use vstd::prelude::macros::*;
use verus_state_machines_macros::state_machine;
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

pub uninterp spec(checked) fn page_count() -> nat;

/// Returns the number of Allocation Unit of the disk.
/// Left as an uninterpreted function since it's implementation defined.
pub uninterp spec(checked) fn au_count() -> nat;

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

#[derive(Debug)]
pub enum GenericDiskRequest<A, D> {
    ReadReq{from: A},
    WriteReq{to: A, data: D},
}

impl<A, D> GenericDiskRequest<A, D> {
    pub open spec fn addr(self) -> A
    {
        match self {
            Self::ReadReq{from} => from,
            Self::WriteReq{to, data} => to,
        }
    }
}

impl<A: Copy, D> GenericDiskRequest<A, D> {
    pub exec fn exec_addr(&self) -> (out: A)
        ensures out == self.addr()
    {
        match self {
            Self::ReadReq{from} => *from,
            Self::WriteReq{to, data} => *to,
        }
    }
}

pub type DiskRequest = GenericDiskRequest<Address, RawPage>;

#[derive(Debug)]
pub enum GenericDiskResponse<D> {
    ReadResp{data: D},
    WriteResp{},
}

pub type DiskResponse = GenericDiskResponse<RawPage>;

pub open spec fn empty_requests() -> Map<ID, DiskRequest>
{
    map!{}
}

pub open spec fn empty_responses() -> Map<ID, DiskResponse>
{
    map!{}
}

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
        init requests = empty_requests();
        init responses = empty_responses();
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

pub proof fn inv_next(pre: AsyncDisk::State, post: AsyncDisk::State, lbl: AsyncDisk::Label)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre, post, lbl),
    ensures
        post.inv(),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre, post, lbl, step);
    match step {
        AsyncDisk::Step::disk_ops() => {
            assert(post.requests == pre.requests.union_prefer_right(lbl->requests));
            assert(post.responses == pre.responses.remove_keys(lbl->responses.dom()));
            assert forall |id: ID| #[trigger] post.requests.contains_key(id) implies !post.responses.contains_key(id) by {
                if pre.requests.contains_key(id) {
                    assert(!pre.responses.contains_key(id));
                } else {
                    assert(lbl is DiskOps);
                    assert(lbl->requests.contains_key(id));
                    assert(!pre.responses.contains_key(id));
                }
            };
            assert(post.inv());
        }
        AsyncDisk::Step::process_read(id) => {
            assert(post.requests == pre.requests.remove(id));
            assert(post.responses == pre.responses.insert(id, post.responses[id]));
            assert forall |id2: ID| #[trigger] post.requests.contains_key(id2) implies !post.responses.contains_key(id2) by {
                if id2 == id {
                    assert(!post.requests.contains_key(id));
                } else {
                    vstd::map::axiom_map_remove_different(pre.requests, id2, id);
                    vstd::map::axiom_map_insert_domain(pre.responses, id, post.responses[id]);
                    vstd::map::axiom_map_insert_different(pre.responses, id2, id, post.responses[id]);
                    assert(pre.requests.contains_key(id2));
                    if post.responses.contains_key(id2) {
                        assert(post.responses.dom().contains(id2));
                        assert(pre.responses.dom().insert(id).contains(id2));
                        vstd::set::axiom_set_insert_different(pre.responses.dom(), id2, id);
                        assert(pre.responses.dom().contains(id2));
                        assert(pre.responses.contains_key(id2));
                    }
                    assert(!pre.responses.contains_key(id2));
                }
            };
            assert(post.inv());
        }
        AsyncDisk::Step::process_write(id) => {
            assert(post.requests == pre.requests.remove(id));
            assert(post.responses == pre.responses.insert(id, DiskResponse::WriteResp{}));
            assert forall |id2: ID| #[trigger] post.requests.contains_key(id2) implies !post.responses.contains_key(id2) by {
                if id2 == id {
                    assert(!post.requests.contains_key(id));
                } else {
                    vstd::map::axiom_map_remove_different(pre.requests, id2, id);
                    vstd::map::axiom_map_insert_domain(pre.responses, id, DiskResponse::WriteResp{});
                    vstd::map::axiom_map_insert_different(pre.responses, id2, id, DiskResponse::WriteResp{});
                    assert(pre.requests.contains_key(id2));
                    if post.responses.contains_key(id2) {
                        assert(post.responses.dom().contains(id2));
                        assert(pre.responses.dom().insert(id).contains(id2));
                        vstd::set::axiom_set_insert_different(pre.responses.dom(), id2, id);
                        assert(pre.responses.dom().contains(id2));
                        assert(pre.responses.contains_key(id2));
                    }
                    assert(!pre.responses.contains_key(id2));
                }
            };
            assert(post.inv());
        }
        AsyncDisk::Step::crash() => {
            assert(post.requests == Map::<ID, DiskRequest>::empty());
            assert(post.responses == Map::<ID, DiskResponse>::empty());
            assert(post.inv());
        }
        _ => { assert(false); }
    }
}

} // end of !verus
