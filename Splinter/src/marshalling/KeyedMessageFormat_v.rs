// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::marshalling::Marshalling_v::{Deepview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::StaticallySized_v::StaticallySized;
use crate::marshalling::Wrappable_v::*;

verus! {

pub struct KeyedMessageFormatWrappable {}
impl Wrappable for KeyedMessageFormatWrappable {
    type AF = IntFormat::<u64>;
    type BF = IntFormat::<u64>;
    type DV = KeyedMessage;
    type U = KeyedMessage;

    open spec fn value_marshallable(value: KeyedMessage) -> bool
    {
        // We aren't gonna need Delta values for a long time
        value.message is Define
    }

    open spec fn to_pair(value: KeyedMessage) -> (int, int)
    {
        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { 0 },
        };
        (value.key.0 as int, message_data as int)
    }

    open spec fn from_pair(pair: (int, int)) -> (value: KeyedMessage)
    {
        KeyedMessage{ key: Key(pair.0 as u64), message: Message::Define{value: Value(pair.1 as u64)}}
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &KeyedMessage) -> (pair: (u64, u64))
    {
        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { assert(false); 0 },
        };
        let pair = (value.key.0, message_data);
        assert( Self::to_pair((*value).deepv()) == pair.deepv() );  // verus #1534
        pair
    }

    exec fn exec_from_pair(pair: (u64, u64)) -> (km: KeyedMessage)
    {
        KeyedMessage{ key: Key(pair.0), message: Message::Define{value: Value(pair.1)}}
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (IntFormat::new(), IntFormat::new())
    }
}

// impl UniformSized for KeyedMessageFormat {
//     open spec fn uniform_size(&self) -> (sz: usize) {
//         (u64::uniform_size() + u64::uniform_size()) as usize
//     }
// 
//     proof fn uniform_size_ensures(&self)
//     ensures 0 < self.uniform_size()
//     { }
// 
//     exec fn exec_uniform_size(&self) -> (sz: usize)
//     ensures sz == self.uniform_size()
//     {
//         u64::exec_uniform_size() + u64::exec_uniform_size()
//     }
// }

pub type KeyedMessageFormat = WrappableFormat<KeyedMessageFormatWrappable>;

} //verus!
