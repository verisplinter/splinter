// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! ISuperblock marshaller generated using the struct_marshaller_2! macro

use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::marshalling::StructMarshalMacro_v::identity;
use crate::marshalling::JournalSnapshot2Format_v::JournalSnapshot2Format;
use crate::marshalling::KeyValueFormat_v::KeyValueFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::SuperblockTypes_v::{ASuperblock, ISuperblock};
use crate::implementation::CachedJournal_v::JournalSnapShot;
use crate::implementation::JournalImpl_v::JournalSnapshot;
use crate::disk::GenericDisk_v::Address;
use crate::disk::GenericDisk_v::IAddress;

struct_marshaller_2! {
    format_name: ISuperblock3Format,
    impl_type: ISuperblock,
    spec_type: ASuperblock,
    field1: {
        impl_field: journal_snapshot,
        spec_field: journal,
        formatter_type: JournalSnapshot2Format,
        formatter_spec_new: JournalSnapshot2Format::spec_new(),
        formatter_new: JournalSnapshot2Format::new(),
        parse_fn: identity,
        marshallable_fn: identity,
    },
    field2: {
        impl_field: store,
        spec_field: store,
        formatter_type: ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>,
        formatter_spec_new: ResizableUniformSizedElementSeqFormat::spec_new(
            KeyValueFormat::spec_new(),
            IntFormat::<u8>::spec_new(),
            200
        ),
        formatter_new: ResizableUniformSizedElementSeqFormat::new(
            KeyValueFormat::new(),
            IntFormat::<u8>::new(),
            200
        ),
        parse_fn: identity,
        marshallable_fn: identity,
    }
}

