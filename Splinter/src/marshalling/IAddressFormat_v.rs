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
use crate::disk::GenericDisk_v::IAU;
use crate::disk::GenericDisk_v::IPage;
use crate::disk::GenericDisk_v::IAddress;
use crate::disk::GenericDisk_v::Address;
use crate::implementation::JournalTypes_v::*;
use crate::marshalling::WF_v::WF;
use crate::disk::GenericDisk_v::AU;
use crate::disk::GenericDisk_v::Page;

verus! {

pub struct IAddressWrappable {}
impl Wrappable for IAddressWrappable {
    type AF = IntFormat::<IAU>;
    type BF = IntFormat::<IPage>;
    type DV = Address;
    type U = IAddress;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        // self.b_fmt.marshallable(value.msg_history)
        &&& true
    }

    open spec fn to_pair(value: Address) -> (int, int)
    {
        (value.au as int, value.page as int)
    }

    open spec fn from_pair(pair: (int, int)) -> (value: Address)
    {
        Address{au: pair.0 as AU, page: pair.1 as Page}
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &IAddress) -> (pair: (IAU, IPage))
    {
        let pair = (value.au, value.page);
        assert( Self::to_pair(value.parsedv()).0 == pair.parsedv().0 ); // extn
        assert( pair.wf() );    // TODO(jonh)
        pair
    }

    exec fn exec_from_pair(pair: (IAU, IPage)) -> (out: IAddress)
    {
        IAddress{au: pair.0, page: pair.1}
    }

    open spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    {
        (IntFormat::spec_new(), IntFormat::spec_new())
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (IntFormat::new(), IntFormat::new())
    }
}

pub type IAddressFormat = WrappableFormat<IAddressWrappable>;

} //verus!
