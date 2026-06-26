// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::allocation_layer::AllocationBranch_v::BranchNode as AllocationBranchNode;
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer};
use crate::implementation::IBranchNode_v::{BranchNodeImage, IBranchNode, iaddr_seq, iopt_addr};
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::KeyFormat_v::KeyFormat;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::spec::AsyncDisk_t::{AU, RawPage};
use crate::spec::ImplDisk_t::IAU;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message, Value};
use crate::trusted::ClientAPI_t::BLOCK_SIZE;

verus! {

pub const BRANCH_NODE_LEAF_TAG: u8 = 0;
pub const BRANCH_NODE_INDEX_TAG: u8 = 1;
pub const BRANCH_NODE_AUX_TAG: u8 = 2;

pub const BRANCH_MESSAGE_DEFINE_TAG: u8 = 0;
pub const BRANCH_MESSAGE_UPDATE_TAG: u8 = 1;

pub struct BranchMessageFormat {
    pub payload_fmt: NatFormat<u64>,
}

impl BranchMessageFormat {
    pub open spec fn spec_new() -> Self
    {
        Self { payload_fmt: NatFormat::spec_new() }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        Self { payload_fmt: NatFormat::new() }
    }
}

impl UniformSized for BranchMessageFormat {
    open spec fn us_valid(&self) -> bool
    {
        &&& self.payload_fmt.us_valid()
        &&& self.payload_fmt.uniform_size() + 1 <= usize::MAX
    }

    open spec fn uniform_size(&self) -> usize
    {
        (self.payload_fmt.uniform_size() + 1) as usize
    }

    proof fn uniform_size_ensures(&self)
    {
        self.payload_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        1 + self.payload_fmt.exec_uniform_size()
    }
}

impl Marshal for BranchMessageFormat {
    type DV = Message;
    type U = Message;

    open spec fn valid(&self) -> bool
    {
        self.payload_fmt.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& data.len() >= self.uniform_size()
        &&& (data[0] == BRANCH_MESSAGE_DEFINE_TAG || data[0] == BRANCH_MESSAGE_UPDATE_TAG)
        &&& self.payload_fmt.parsable(data.subrange(1, 1 + self.payload_fmt.uniform_size() as int))
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let payload = self.payload_fmt.parse(data.subrange(1, 1 + self.payload_fmt.uniform_size() as int)) as u64;
        if data[0] == BRANCH_MESSAGE_DEFINE_TAG {
            Message::Define { value: Value(payload) }
        } else {
            Message::Update { delta: Delta(payload) }
        }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        match value {
            Message::Define { value } => self.payload_fmt.marshallable(value.0 as nat),
            Message::Update { delta } => self.payload_fmt.marshallable(delta.0 as nat),
        }
    }

    open spec fn impl_marshallable(&self, value: Self::U) -> bool
    {
        match value {
            Message::Define { value: Value(v) } => self.payload_fmt.impl_marshallable(v),
            Message::Update { delta: Delta(v) } => self.payload_fmt.impl_marshallable(v),
        }
    }

    open spec fn spec_size(&self, _value: Self::DV) -> usize
    {
        self.uniform_size()
    }

    exec fn exec_size(&self, _value: &Self::U) -> (sz: usize)
    {
        self.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        match value {
            Message::Define { value: Value(v) } => {
                data.set(start, BRANCH_MESSAGE_DEFINE_TAG);
                let end = self.payload_fmt.exec_marshall(v, data, start + 1);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    let body = subr.subrange(1, 1 + self.payload_fmt.uniform_size() as int);
                    assert(body == data@.subrange((start + 1) as int, end as int));
                    assert(self.payload_fmt.parsable(body));
                    assert(self.payload_fmt.parse(body) == (*v as nat));
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == Message::Define { value: Value(*v) });
                    assert(self.parse(subr) == value.parsedv());
                }
                end
            }
            Message::Update { delta: Delta(v) } => {
                data.set(start, BRANCH_MESSAGE_UPDATE_TAG);
                let end = self.payload_fmt.exec_marshall(v, data, start + 1);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    let body = subr.subrange(1, 1 + self.payload_fmt.uniform_size() as int);
                    assert(body == data@.subrange((start + 1) as int, end as int));
                    assert(self.payload_fmt.parsable(body));
                    assert(self.payload_fmt.parse(body) == (*v as nat));
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == Message::Update { delta: Delta(*v) });
                    assert(self.parse(subr) == value.parsedv());
                }
                end
            }
        }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < self.exec_uniform_size() {
            proof {
                assert(!self.parsable(slice@.i(data@)));
            }
            return None;
        }
        let tag = data[slice.start];
        if tag != BRANCH_MESSAGE_DEFINE_TAG && tag != BRANCH_MESSAGE_UPDATE_TAG {
            proof {
                assert(!self.parsable(slice@.i(data@)));
            }
            return None;
        }
        let payload_slice = slice.subslice(1, 1 + self.payload_fmt.exec_uniform_size());
        match self.payload_fmt.try_parse(&payload_slice, data) {
            None => {
                proof {
                    let idata = slice@.i(data@);
                    assert(payload_slice@.i(data@) == idata.subrange(1, 1 + self.payload_fmt.uniform_size() as int));
                    assert(!self.payload_fmt.parsable(payload_slice@.i(data@)));
                    assert(!self.parsable(idata));
                }
                None
            }
            Some(v) => {
                let msg =
                    if tag == BRANCH_MESSAGE_DEFINE_TAG {
                        Message::Define { value: Value(v) }
                    } else {
                        Message::Update { delta: Delta(v) }
                    };
                proof {
                    let idata = slice@.i(data@);
                    assert(payload_slice@.i(data@) == idata.subrange(1, 1 + self.payload_fmt.uniform_size() as int));
                    assert(self.parsable(idata));
                    assert(msg.parsedv() == self.parse(idata));
                    assert(msg.wf());
                }
                Some(msg)
            }
        }
    }
}

impl UniformSizedMarshal for BranchMessageFormat {
    proof fn uniform_size_matches_spec_size(self: &Self)
    {
        assert forall |value: Message| #[trigger] self.spec_size(value) == self.uniform_size() by {
        }
    }
}

#[derive(Clone, Copy, Debug)]
#[verifier::ext_equal]
pub struct IBranchLeafEntry {
    pub key: Key,
    pub msg: Message,
}

impl WF for IBranchLeafEntry {
    open spec fn wf(&self) -> bool
    {
        &&& self.key.wf()
        &&& self.msg.wf()
    }
}

impl Parsedview<IBranchLeafEntry> for IBranchLeafEntry {
    open spec fn parsedv(&self) -> IBranchLeafEntry
    {
        *self
    }
}

#[verifier::ext_equal]
pub struct BranchIndexMetaImage {
    pub first_child: Address,
    pub aux_ptr: Pointer,
}

#[derive(Clone, Copy, Debug)]
#[verifier::ext_equal]
pub struct IBranchIndexMeta {
    pub first_child: IAddress,
    pub aux_ptr: Option<IAddress>,
}

impl WF for IBranchIndexMeta {
    open spec fn wf(&self) -> bool
    {
        &&& self.first_child.wf()
        &&& self.aux_ptr.wf()
    }
}

impl Parsedview<BranchIndexMetaImage> for IBranchIndexMeta {
    open spec fn parsedv(&self) -> BranchIndexMetaImage
    {
        BranchIndexMetaImage { first_child: self.first_child@, aux_ptr: iopt_addr(self.aux_ptr) }
    }
}

#[verifier::ext_equal]
pub struct BranchIndexRouteImage {
    pub pivot: Key,
    pub child: Address,
}

#[derive(Clone, Copy, Debug)]
#[verifier::ext_equal]
pub struct IBranchIndexRoute {
    pub pivot: Key,
    pub child: IAddress,
}

impl WF for IBranchIndexRoute {
    open spec fn wf(&self) -> bool
    {
        &&& self.pivot.wf()
        &&& self.child.wf()
    }
}

impl Parsedview<BranchIndexRouteImage> for IBranchIndexRoute {
    open spec fn parsedv(&self) -> BranchIndexRouteImage
    {
        BranchIndexRouteImage { pivot: self.pivot, child: self.child@ }
    }
}

proof fn branch_leaf_entry_wf_proof(
    key: Key,
    msg: Message,
    entry: IBranchLeafEntry,
)
    requires
        key.wf(),
        msg.wf(),
        entry.key == key,
        entry.msg == msg,
    ensures
        entry.wf(),
{
}

proof fn branch_leaf_entry_postcondition_proof(
    fmt: &IBranchLeafEntryFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: Key,
    field2_slice: &Slice,
    field2_value: Message,
    result: IBranchLeafEntry,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.key == field1_value,
        result.msg == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<Key>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<Message>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

proof fn branch_index_meta_wf_proof(
    first_child: IAddress,
    aux_ptr: Option<IAddress>,
    meta: IBranchIndexMeta,
)
    requires
        first_child.wf(),
        aux_ptr.wf(),
        meta.first_child == first_child,
        meta.aux_ptr == aux_ptr,
    ensures
        meta.wf(),
{
}

proof fn branch_index_meta_postcondition_proof(
    fmt: &IBranchIndexMetaFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: IAddress,
    field2_slice: &Slice,
    field2_value: Option<IAddress>,
    result: IBranchIndexMeta,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.first_child == field1_value,
        result.aux_ptr == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<Address>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<Pointer>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

proof fn branch_index_route_wf_proof(
    pivot: Key,
    child: IAddress,
    route: IBranchIndexRoute,
)
    requires
        pivot.wf(),
        child.wf(),
        route.pivot == pivot,
        route.child == child,
    ensures
        route.wf(),
{
}

proof fn branch_index_route_postcondition_proof(
    fmt: &IBranchIndexRouteFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: Key,
    field2_slice: &Slice,
    field2_value: IAddress,
    result: IBranchIndexRoute,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.pivot == field1_value,
        result.child == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<Key>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<Address>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

pub open spec fn leaf_entry_seq(keys: Seq<Key>, msgs: Seq<Message>) -> Seq<IBranchLeafEntry>
    recommends
        keys.len() == msgs.len(),
{
    Seq::new(keys.len() as nat, |i: int| IBranchLeafEntry { key: keys[i], msg: msgs[i] })
}

pub open spec fn route_image_seq(pivots: Seq<Key>, children: Seq<Address>) -> Seq<BranchIndexRouteImage>
    recommends
        children.len() == pivots.len() + 1,
{
    Seq::new(pivots.len() as nat, |i: int| BranchIndexRouteImage { pivot: pivots[i], child: children[i + 1] })
}

pub open spec fn route_impl_seq(pivots: Seq<Key>, children: Seq<IAddress>) -> Seq<IBranchIndexRoute>
    recommends
        children.len() == pivots.len() + 1,
{
    Seq::new(pivots.len() as nat, |i: int| IBranchIndexRoute { pivot: pivots[i], child: children[i + 1] })
}

pub proof fn route_impl_seq_parsedv(pivots: Seq<Key>, children: Seq<IAddress>)
    requires
        children.len() == pivots.len() + 1,
    ensures
        route_impl_seq(pivots, children).map(|i: int, route: IBranchIndexRoute| route.parsedv())
            == route_image_seq(pivots, iaddr_seq(children)),
{
    assert forall |i: int| #![trigger route_impl_seq(pivots, children)[i]]
        0 <= i < pivots.len()
        implies route_impl_seq(pivots, children)[i].parsedv() == route_image_seq(pivots, iaddr_seq(children))[i]
    by {
        assert(route_impl_seq(pivots, children)[i].parsedv() == route_image_seq(pivots, iaddr_seq(children))[i]);
    }
}

pub open spec fn leaf_entries_image(entries: Seq<IBranchLeafEntry>) -> BranchNodeImage
{
    BranchNodeImage::Leaf {
        keys: entries.map(|i: int, entry: IBranchLeafEntry| entry.key),
        msgs: entries.map(|i: int, entry: IBranchLeafEntry| entry.msg),
    }
}

pub open spec fn index_routes_image(meta: BranchIndexMetaImage, routes: Seq<BranchIndexRouteImage>) -> BranchNodeImage
{
    BranchNodeImage::Index {
        pivots: routes.map(|i: int, route: BranchIndexRouteImage| route.pivot),
        children: seq![meta.first_child] + routes.map(|i: int, route: BranchIndexRouteImage| route.child),
        aux_ptr: meta.aux_ptr,
    }
}

pub open spec fn summary_aus_image(summary_aus: Seq<AU>) -> BranchNodeImage
{
    BranchNodeImage::Auxiliary { summary_aus }
}

fn unzip_leaf_entries(entries: Vec<IBranchLeafEntry>) -> (out: (Vec<Key>, Vec<Message>))
    ensures
        out.0@ == entries@.map(|i: int, entry: IBranchLeafEntry| entry.key),
        out.1@ == entries@.map(|i: int, entry: IBranchLeafEntry| entry.msg),
{
    let mut keys = Vec::new();
    let mut msgs = Vec::new();
    let mut idx = 0usize;
    while idx < entries.len()
        invariant
            idx <= entries.len(),
            keys@ == entries@.subrange(0, idx as int).map(|i: int, entry: IBranchLeafEntry| entry.key),
            msgs@ == entries@.subrange(0, idx as int).map(|i: int, entry: IBranchLeafEntry| entry.msg),
        decreases entries.len() - idx,
    {
        keys.push(entries[idx].key);
        msgs.push(entries[idx].msg);
        idx += 1;
    }
    (keys, msgs)
}

fn zip_leaf_entries(keys: &Vec<Key>, msgs: &Vec<Message>) -> (out: Vec<IBranchLeafEntry>)
    requires
        keys.len() == msgs.len(),
    ensures
        out@ == leaf_entry_seq(keys@, msgs@),
{
    let mut out = Vec::new();
    let mut idx = 0usize;
    while idx < keys.len()
        invariant
            idx <= keys.len(),
            idx <= msgs.len(),
            out@ == leaf_entry_seq(keys@.subrange(0, idx as int), msgs@.subrange(0, idx as int)),
        decreases keys.len() - idx,
    {
        out.push(IBranchLeafEntry { key: keys[idx], msg: msgs[idx] });
        idx += 1;
    }
    out
}

fn unzip_index_routes(first_child: IAddress, routes: Vec<IBranchIndexRoute>) -> (out: (Vec<Key>, Vec<IAddress>))
    ensures
        out.0@ == routes@.map(|i: int, route: IBranchIndexRoute| route.pivot),
        out.1@ == seq![first_child] + routes@.map(|i: int, route: IBranchIndexRoute| route.child),
        out.1.len() == out.0.len() + 1,
{
    let mut pivots = Vec::new();
    let mut children = Vec::new();
    children.push(first_child);
    let mut idx = 0usize;
    while idx < routes.len()
        invariant
            idx <= routes.len(),
            pivots@ == routes@.subrange(0, idx as int).map(|i: int, route: IBranchIndexRoute| route.pivot),
            children@ == seq![first_child] + routes@.subrange(0, idx as int).map(|i: int, route: IBranchIndexRoute| route.child),
            children.len() == pivots.len() + 1,
        decreases routes.len() - idx,
    {
        pivots.push(routes[idx].pivot);
        children.push(routes[idx].child);
        idx += 1;
    }
    (pivots, children)
}

fn zip_index_routes(pivots: &Vec<Key>, children: &Vec<IAddress>) -> (out: Vec<IBranchIndexRoute>)
    requires
        children.len() == pivots.len() + 1,
    ensures
        out@ == route_impl_seq(pivots@, children@),
{
    let mut out = Vec::new();
    let mut idx = 0usize;
    while idx < pivots.len()
        invariant
            idx <= pivots.len(),
            children.len() == pivots.len() + 1,
            out@ == route_impl_seq(pivots@.subrange(0, idx as int), children@.subrange(0, (idx + 1) as int)),
        decreases pivots.len() - idx,
    {
        out.push(IBranchIndexRoute { pivot: pivots[idx], child: children[idx + 1] });
        idx += 1;
    }
    out
}

} // verus!

struct_marshaller_2! {
    format_name: IBranchLeafEntryFormat,
    impl_type: IBranchLeafEntry,
    spec_type: IBranchLeafEntry,
    wf_proof: branch_leaf_entry_wf_proof,
    postcondition_proof: branch_leaf_entry_postcondition_proof,
    field1: {
        impl_field: key,
        spec_field: key,
        formatter_type: KeyFormat,
        formatter_spec_new: KeyFormat::spec_new(),
        formatter_new: KeyFormat::new(),
    },
    field2: {
        impl_field: msg,
        spec_field: msg,
        formatter_type: BranchMessageFormat,
        formatter_spec_new: BranchMessageFormat::spec_new(),
        formatter_new: BranchMessageFormat::new(),
    }
}

struct_marshaller_2! {
    format_name: IBranchIndexMetaFormat,
    impl_type: IBranchIndexMeta,
    spec_type: BranchIndexMetaImage,
    wf_proof: branch_index_meta_wf_proof,
    postcondition_proof: branch_index_meta_postcondition_proof,
    field1: {
        impl_field: first_child,
        spec_field: first_child,
        formatter_type: IAddressFormat,
        formatter_spec_new: IAddressFormat::spec_new(),
        formatter_new: IAddressFormat::new(),
    },
    field2: {
        impl_field: aux_ptr,
        spec_field: aux_ptr,
        formatter_type: OptionFormat<IAddressFormat>,
        formatter_spec_new: OptionFormat::spec_new(IAddressFormat::spec_new()),
        formatter_new: OptionFormat::new(IAddressFormat::new()),
    }
}

struct_marshaller_2! {
    format_name: IBranchIndexRouteFormat,
    impl_type: IBranchIndexRoute,
    spec_type: BranchIndexRouteImage,
    wf_proof: branch_index_route_wf_proof,
    postcondition_proof: branch_index_route_postcondition_proof,
    field1: {
        impl_field: pivot,
        spec_field: pivot,
        formatter_type: KeyFormat,
        formatter_spec_new: KeyFormat::spec_new(),
        formatter_new: KeyFormat::new(),
    },
    field2: {
        impl_field: child,
        spec_field: child,
        formatter_type: IAddressFormat,
        formatter_spec_new: IAddressFormat::spec_new(),
        formatter_new: IAddressFormat::new(),
    }
}

verus! {

pub type BranchLeafEntriesFormat = ResizableUniformSizedElementSeqFormat<IBranchLeafEntryFormat, u8>;
pub type BranchIndexRoutesFormat = ResizableUniformSizedElementSeqFormat<IBranchIndexRouteFormat, u8>;
pub type BranchSummaryAusFormat = ResizableUniformSizedElementSeqFormat<NatFormat<u32>, u8>;

pub struct IBranchNodeFormat {
    pub leaf_fmt: BranchLeafEntriesFormat,
    pub index_meta_fmt: IBranchIndexMetaFormat,
    pub index_routes_fmt: BranchIndexRoutesFormat,
    pub aux_fmt: BranchSummaryAusFormat,
}

impl IBranchNodeFormat {
    pub open spec fn spec_new() -> Self
    {
        let body_size = (BLOCK_SIZE - 1) as usize;
        let index_meta_fmt = IBranchIndexMetaFormat::spec_new();
        let index_routes_body_size = (body_size - index_meta_fmt.uniform_size()) as usize;
        Self {
            leaf_fmt: BranchLeafEntriesFormat::spec_new(IBranchLeafEntryFormat::spec_new(), IntFormat::<u8>::spec_new(), body_size),
            index_meta_fmt,
            index_routes_fmt: BranchIndexRoutesFormat::spec_new(IBranchIndexRouteFormat::spec_new(), IntFormat::<u8>::spec_new(), index_routes_body_size),
            aux_fmt: BranchSummaryAusFormat::spec_new(NatFormat::<u32>::spec_new(), IntFormat::<u8>::spec_new(), body_size),
        }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        let body_size = BLOCK_SIZE - 1;
        let index_meta_fmt = IBranchIndexMetaFormat::new();
        let index_routes_body_size = body_size - index_meta_fmt.exec_uniform_size();
        Self {
            leaf_fmt: BranchLeafEntriesFormat::new(IBranchLeafEntryFormat::new(), IntFormat::<u8>::new(), body_size),
            index_meta_fmt,
            index_routes_fmt: BranchIndexRoutesFormat::new(IBranchIndexRouteFormat::new(), IntFormat::<u8>::new(), index_routes_body_size),
            aux_fmt: BranchSummaryAusFormat::new(NatFormat::<u32>::new(), IntFormat::<u8>::new(), body_size),
        }
    }
}

impl UniformSized for IBranchNodeFormat {
    open spec fn us_valid(&self) -> bool
    {
        &&& self.leaf_fmt.us_valid()
        &&& self.index_meta_fmt.us_valid()
        &&& self.index_routes_fmt.us_valid()
        &&& self.aux_fmt.us_valid()
        &&& self.leaf_fmt.uniform_size() == self.aux_fmt.uniform_size()
        &&& self.index_meta_fmt.uniform_size() + self.index_routes_fmt.uniform_size() == self.leaf_fmt.uniform_size()
        &&& self.leaf_fmt.uniform_size() + 1 == BLOCK_SIZE
    }

    open spec fn uniform_size(&self) -> usize
    {
        (self.leaf_fmt.uniform_size() + 1) as usize
    }

    proof fn uniform_size_ensures(&self)
    {
        self.leaf_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    {
        1 + self.leaf_fmt.exec_uniform_size()
    }
}

impl Marshal for IBranchNodeFormat {
    type DV = BranchNodeImage;
    type U = IBranchNode;

    open spec fn valid(&self) -> bool
    {
        &&& self.us_valid()
        &&& self.leaf_fmt.valid()
        &&& self.index_meta_fmt.valid()
        &&& self.index_routes_fmt.valid()
        &&& self.aux_fmt.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& data.len() >= self.uniform_size()
        &&& match data[0] {
            BRANCH_NODE_LEAF_TAG => self.leaf_fmt.parsable(data.subrange(1, 1 + self.leaf_fmt.uniform_size() as int)),
            BRANCH_NODE_INDEX_TAG => {
                let meta_end = 1 + self.index_meta_fmt.uniform_size() as int;
                &&& self.index_meta_fmt.parsable(data.subrange(1, meta_end))
                &&& self.index_routes_fmt.parsable(data.subrange(meta_end, meta_end + self.index_routes_fmt.uniform_size() as int))
            }
            BRANCH_NODE_AUX_TAG => self.aux_fmt.parsable(data.subrange(1, 1 + self.aux_fmt.uniform_size() as int)),
            _ => false,
        }
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        match data[0] {
            BRANCH_NODE_LEAF_TAG => leaf_entries_image(self.leaf_fmt.parse(data.subrange(1, 1 + self.leaf_fmt.uniform_size() as int))),
            BRANCH_NODE_INDEX_TAG => {
                let meta_end = 1 + self.index_meta_fmt.uniform_size() as int;
                let meta = self.index_meta_fmt.parse(data.subrange(1, meta_end));
                let routes = self.index_routes_fmt.parse(data.subrange(meta_end, meta_end + self.index_routes_fmt.uniform_size() as int));
                index_routes_image(meta, routes)
            }
            BRANCH_NODE_AUX_TAG => summary_aus_image(self.aux_fmt.parse(data.subrange(1, 1 + self.aux_fmt.uniform_size() as int))),
            _ => arbitrary(),
        }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        match value {
            BranchNodeImage::Leaf { keys, msgs } => {
                &&& keys.len() == msgs.len()
                &&& self.leaf_fmt.marshallable(leaf_entry_seq(keys, msgs))
            }
            BranchNodeImage::Index { pivots, children, aux_ptr } => {
                &&& children.len() == pivots.len() + 1
                &&& self.index_meta_fmt.marshallable(BranchIndexMetaImage { first_child: children[0], aux_ptr })
                &&& self.index_routes_fmt.marshallable(route_image_seq(pivots, children))
            }
            BranchNodeImage::Auxiliary { summary_aus } => self.aux_fmt.marshallable(summary_aus),
        }
    }

    open spec fn impl_marshallable(&self, value: Self::U) -> bool
    {
        &&& value.wf()
        &&& match value {
            IBranchNode::Leaf { keys, msgs } => {
                &&& keys.len() == msgs.len()
                &&& self.leaf_fmt.marshallable(leaf_entry_seq(keys@, msgs@))
                &&& forall |i: int| #![auto] 0 <= i < keys.len()
                    ==> self.leaf_fmt.eltf.impl_marshallable(IBranchLeafEntry { key: keys[i], msg: msgs[i] })
            }
            IBranchNode::Index { pivots, children, aux_ptr } => {
                &&& children.len() == pivots.len() + 1
                &&& self.index_meta_fmt.impl_marshallable(IBranchIndexMeta { first_child: children[0], aux_ptr })
                &&& self.index_routes_fmt.marshallable(route_image_seq(pivots@, iaddr_seq(children@)))
                &&& forall |i: int| 0 <= i < pivots.len()
                    ==> self.index_routes_fmt.eltf.impl_marshallable(IBranchIndexRoute { pivot: pivots[i], child: children[i + 1] })
            }
            IBranchNode::Auxiliary { summary_aus } => {
                &&& self.aux_fmt.marshallable(summary_aus@.map(|i: int, au: IAU| au as nat))
                &&& forall |i: int| #![auto] 0 <= i < summary_aus.len()
                    ==> self.aux_fmt.eltf.impl_marshallable(summary_aus[i])
            }
        }
    }

    open spec fn spec_size(&self, _value: Self::DV) -> usize
    {
        self.uniform_size()
    }

    exec fn exec_size(&self, _value: &Self::U) -> (sz: usize)
    {
        self.exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        match value {
            IBranchNode::Leaf { keys, msgs } => {
                data.set(start, BRANCH_NODE_LEAF_TAG);
                let entries = zip_leaf_entries(keys, msgs);
                let end = self.leaf_fmt.exec_marshall(&entries, data, start + 1);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    let body = data@.subrange((start + 1) as int, end as int);
                    let parsed = leaf_entries_image(entries@);
                    assert(subr.subrange(1, 1 + self.leaf_fmt.uniform_size() as int) == body);
                    assert(self.leaf_fmt.parsable(body));
                    assert(self.leaf_fmt.parse(body) == entries@);
                    assert(self.parse(subr) =~= parsed);
                    assert(value.parsedv() =~= parsed);
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
                end
            }
            IBranchNode::Index { pivots, children, aux_ptr } => {
                assert(children.len() > 0);
                data.set(start, BRANCH_NODE_INDEX_TAG);
                let meta = IBranchIndexMeta { first_child: children[0], aux_ptr: *aux_ptr };
                let meta_end = self.index_meta_fmt.exec_marshall(&meta, data, start + 1);
                let ghost mid_data = data@;
                let routes = zip_index_routes(pivots, children);
                let end = self.index_routes_fmt.exec_marshall(&routes, data, meta_end);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    let local_meta_end = 1 + self.index_meta_fmt.uniform_size() as int;
                    let meta_body = data@.subrange((start + 1) as int, meta_end as int);
                    let routes_body = data@.subrange(meta_end as int, end as int);
                    let parsed = index_routes_image(self.index_meta_fmt.parse(meta_body), routes.parsedv());
                    route_impl_seq_parsedv(pivots@, children@);
                    assert(meta_end == start + 1 + self.index_meta_fmt.spec_size(meta.parsedv()));
                    assert(subr[0] == BRANCH_NODE_INDEX_TAG);
                    assert(subr.subrange(1, local_meta_end) == meta_body);
                    assert(subr.subrange(local_meta_end, local_meta_end + self.index_routes_fmt.uniform_size() as int) == routes_body);
                    assert(mid_data.subrange((start + 1) as int, meta_end as int) == data@.subrange((start + 1) as int, meta_end as int));
                    assert(routes.parsedv() == route_image_seq(pivots@, iaddr_seq(children@)));
                    assert(self.index_meta_fmt.parsable(meta_body));
                    assert(self.index_meta_fmt.parse(mid_data.subrange((start + 1) as int, meta_end as int)) == meta.parsedv());
                    assert(self.index_meta_fmt.parse(meta_body).first_child == meta.first_child@);
                    assert(self.index_meta_fmt.parse(meta_body).aux_ptr == iopt_addr(meta.aux_ptr));
                    assert(self.index_routes_fmt.parsable(routes_body));
                    assert(self.index_routes_fmt.parse(routes_body) == routes.parsedv());
                    assert(self.parse(subr) =~= parsed);
                    assert(value.parsedv() =~= parsed);
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
                end
            }
            IBranchNode::Auxiliary { summary_aus } => {
                data.set(start, BRANCH_NODE_AUX_TAG);
                let end = self.aux_fmt.exec_marshall(summary_aus, data, start + 1);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    let body = data@.subrange((start + 1) as int, end as int);
                    let parsed_seq = Parsedview::<Seq<AU>>::parsedv(summary_aus);
                    let parsed = summary_aus_image(parsed_seq);
                    assert(subr[0] == BRANCH_NODE_AUX_TAG);
                    assert(subr.subrange(1, 1 + self.aux_fmt.uniform_size() as int) == body);
                    assert(self.aux_fmt.parsable(body));
                    assert(self.aux_fmt.parse(body) == parsed_seq);
                    assert(self.parse(subr) =~= parsed);
                    assert(value.parsedv() =~= parsed);
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
                end
            }
        }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < self.exec_uniform_size() {
            proof {
                assert(!self.parsable(slice@.i(data@)));
            }
            return None;
        }
        let tag = data[slice.start];
        match tag {
            BRANCH_NODE_LEAF_TAG => {
                let body_slice = slice.subslice(1, 1 + self.leaf_fmt.exec_uniform_size());
                match self.leaf_fmt.try_parse(&body_slice, data) {
                    None => {
                        proof {
                            let idata = slice@.i(data@);
                            assert(body_slice@.i(data@) == idata.subrange(1, 1 + self.leaf_fmt.uniform_size() as int));
                            assert(!self.leaf_fmt.parsable(body_slice@.i(data@)));
                            assert(!self.parsable(idata));
                        }
                        None
                    }
                    Some(entries) => {
                        let (keys, msgs) = unzip_leaf_entries(entries);
                        let node = IBranchNode::Leaf { keys, msgs };
                        proof {
                            let idata = slice@.i(data@);
                            let parsed = leaf_entries_image(entries@);
                            assert(body_slice@.i(data@) == idata.subrange(1, 1 + self.leaf_fmt.uniform_size() as int));
                            assert(self.parsable(idata));
                            assert(node.parsedv() =~= parsed);
                            assert(self.parse(idata) =~= parsed);
                            assert(node.parsedv() == self.parse(idata));
                            assert(node.wf());
                        }
                        Some(node)
                    }
                }
            }
            BRANCH_NODE_INDEX_TAG => {
                let meta_size = self.index_meta_fmt.exec_uniform_size();
                let meta_slice = slice.subslice(1, 1 + meta_size);
                let routes_slice = slice.subslice(1 + meta_size, 1 + meta_size + self.index_routes_fmt.exec_uniform_size());
                match self.index_meta_fmt.try_parse(&meta_slice, data) {
                    None => {
                        proof {
                            let idata = slice@.i(data@);
                            let meta_end = 1 + self.index_meta_fmt.uniform_size() as int;
                            assert(meta_slice@.i(data@) == idata.subrange(1, meta_end));
                            assert(!self.index_meta_fmt.parsable(meta_slice@.i(data@)));
                            assert(!self.parsable(idata));
                        }
                        None
                    }
                    Some(meta) => {
                        match self.index_routes_fmt.try_parse(&routes_slice, data) {
                            None => {
                                proof {
                                    let idata = slice@.i(data@);
                                    let meta_end = 1 + self.index_meta_fmt.uniform_size() as int;
                                    assert(routes_slice@.i(data@) == idata.subrange(meta_end, meta_end + self.index_routes_fmt.uniform_size() as int));
                                    assert(!self.index_routes_fmt.parsable(routes_slice@.i(data@)));
                                    assert(!self.parsable(idata));
                                }
                                None
                            }
                            Some(routes) => {
                                let (pivots, children) = unzip_index_routes(meta.first_child, routes);
                                let node = IBranchNode::Index { pivots, children, aux_ptr: meta.aux_ptr };
                                proof {
                                    let idata = slice@.i(data@);
                                    let parsed = index_routes_image(meta.parsedv(), routes.parsedv());
                                    let meta_end = 1 + self.index_meta_fmt.uniform_size() as int;
                                    assert(meta_slice@.i(data@) == idata.subrange(1, meta_end));
                                    assert(routes_slice@.i(data@) == idata.subrange(meta_end, meta_end + self.index_routes_fmt.uniform_size() as int));
                                    assert(self.parsable(idata));
                                    assert(iaddr_seq(children@) == seq![meta.first_child@] + routes@.map(|i: int, route: IBranchIndexRoute| route.child@));
                                    assert(node.parsedv() =~= parsed);
                                    assert(self.parse(idata) =~= parsed);
                                    assert(node.parsedv() == self.parse(idata));
                                    assert(node.wf());
                                }
                                Some(node)
                            }
                        }
                    }
                }
            }
            BRANCH_NODE_AUX_TAG => {
                let body_slice = slice.subslice(1, 1 + self.aux_fmt.exec_uniform_size());
                match self.aux_fmt.try_parse(&body_slice, data) {
                    None => {
                        proof {
                            let idata = slice@.i(data@);
                            assert(body_slice@.i(data@) == idata.subrange(1, 1 + self.aux_fmt.uniform_size() as int));
                            assert(!self.aux_fmt.parsable(body_slice@.i(data@)));
                            assert(!self.parsable(idata));
                        }
                        None
                    }
                    Some(summary_aus) => {
                        let node = IBranchNode::Auxiliary { summary_aus };
                        proof {
                            let idata = slice@.i(data@);
                            let parsed = summary_aus_image(Parsedview::<Seq<AU>>::parsedv(&summary_aus));
                            assert(body_slice@.i(data@) == idata.subrange(1, 1 + self.aux_fmt.uniform_size() as int));
                            assert(self.parsable(idata));
                            assert(node.parsedv() =~= parsed);
                            assert(self.parse(idata) =~= parsed);
                            assert(node.parsedv() == self.parse(idata));
                            assert(node.wf());
                        }
                        Some(node)
                    }
                }
            }
            _ => {
                proof {
                    assert(!self.parsable(slice@.i(data@)));
                }
                None
            }
        }
    }
}

impl UniformSizedMarshal for IBranchNodeFormat {
    proof fn uniform_size_matches_spec_size(self: &Self)
    {
        assert forall |value: BranchNodeImage| #[trigger] self.spec_size(value) == self.uniform_size() by {
        }
    }
}

pub type BranchNodePageFmt = IBranchNodeFormat;

pub open spec fn raw_page_to_branch_node(raw_page: RawPage) -> AllocationBranchNode
{
    let fmt = IBranchNodeFormat::spec_new();
    if fmt.parsable(raw_page) {
        fmt.parse(raw_page).view()
    } else {
        arbitrary()
    }
}

} // verus!
