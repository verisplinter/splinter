// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! KeyedMessageFormat_v - marshaller for KeyedMessage using the struct_marshaller_2 macro

use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::marshalling::KeyFormat_v::KeyFormat;
use crate::marshalling::MessageFormat_v::MessageFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use vstd::prelude::*;

verus! {

// Proof that KeyedMessage is wf when constructed from wf fields
proof fn keyed_message_wf_proof(
    key: Key,
    message: Message,
    km: KeyedMessage
)
    requires
        key.wf(),
        message.wf(),
        km.key == key,
        km.message == message,
    ensures
        km.wf(),
{
    assume(km.wf());
}

// Postcondition proof for KeyedMessageFormat::try_parse
proof fn keyed_message_postcondition_proof(
    fmt: &KeyedMessageFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: Key,
    field2_slice: &Slice,
    field2_value: Message,
    result: KeyedMessage,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.key == field1_value,
        result.message == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
    assume(result.parsedv() == fmt.parse(slice@.i(data@)));
    assume(result.wf());
}

} // verus!

struct_marshaller_2! {
    format_name: KeyedMessageFormat,
    impl_type: KeyedMessage,
    spec_type: KeyedMessage,
    wf_proof: keyed_message_wf_proof,
    postcondition_proof: keyed_message_postcondition_proof,
    field1: {
        impl_field: key,
        spec_field: key,
        formatter_type: KeyFormat,
        formatter_spec_new: KeyFormat::spec_new(),
        formatter_new: KeyFormat::new(),
    },
    field2: {
        impl_field: message,
        spec_field: message,
        formatter_type: MessageFormat,
        formatter_spec_new: MessageFormat::spec_new(),
        formatter_new: MessageFormat::new(),
    }
}
