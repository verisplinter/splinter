// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::marshalling::Wrappable_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::implementation::JournalTypes_v::*;
use crate::marshalling::WF_v::WF;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::implementation::CachedJournal_v;
use crate::implementation::JournalImpl_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::IAddress;
use crate::disk::GenericDisk_v::Address;

verus! {

pub const JOURNAL_CAPACITY: usize = 200;

// TODO(jonh): move to IAddress defn
impl Parsedview<Address> for IAddress {
    open spec fn parsedv(&self) -> Address { self@ }
}
impl WF for IAddress { }

// Move to KeyedMessage?
impl Parsedview<KeyedMessage> for KeyedMessage {
    open spec fn parsedv(&self) -> KeyedMessage { *self }
}

impl WF for JournalSnapshot { }

pub struct JournalSnapshotWrappable {}
impl Wrappable for JournalSnapshotWrappable {
    type AF = IntFormat::<ILsn>;
    type BF = OptionFormat::<IAddressFormat>;
    type DV = CachedJournal_v::JournalSnapShot;
    type U = JournalSnapshot;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        // self.b_fmt.marshallable(value.msg_history)
        &&& true
    }

    open spec fn to_pair(value: Self::DV) -> (int, Option<Address>)
    {
        (value.boundary_lsn as int, value.freshest_rec)
    }

    open spec fn from_pair(pair: (int, Option<Address>)) -> (value: Self::DV)
    {
        Self::DV{boundary_lsn: pair.0 as LSN, freshest_rec: pair.1}
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &Self::U) -> (pair: (ILsn, Option<IAddress>))
    {
        (value.boundary_lsn, value.freshest_rec)
    }

    exec fn exec_from_pair(pair: (ILsn, Option<IAddress>)) -> (j: JournalSnapshot)
    {
        JournalSnapshot{ boundary_lsn: pair.0, freshest_rec: pair.1 }
    }

    open spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    {
        (IntFormat::spec_new(), OptionFormat::spec_new(IAddressFormat::spec_new()))
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (IntFormat::new(), OptionFormat::new(IAddressFormat::new()))
    }
}

pub type JournalSnapshotFormat = WrappableFormat<JournalSnapshotWrappable>;

} //verus!
