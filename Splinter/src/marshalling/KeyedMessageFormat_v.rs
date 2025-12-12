// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! KeyedMessageFormat_v - marshaller for KeyedMessage using the struct_marshaller_2 macro
//!
//! The macro requires that KeyedMessage::parsedv() is "compositional".
//! KeyedMessage::parsedv() = *self (identity), and each field's parsedv is also identity.

use vstd::prelude::*;
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;
use crate::marshalling::KeyFormat_v::KeyFormat;
use crate::marshalling::MessageFormat_v::MessageFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::marshalling::StructMarshalMacro_v::Compositional2;

struct_marshaller_2! {
    format_name: KeyedMessageFormat,
    impl_type: KeyedMessage,
    spec_type: KeyedMessage,
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
