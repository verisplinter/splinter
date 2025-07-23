// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Deepview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::UniformPairFormat_v::UniformPairMarshal;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::StaticallySized_v::StaticallySized;

verus! {

impl Deepview<(int,int)> for (u64,u64) {
    open spec fn deepv(&self) -> (int,int) { (self.0 as int, self.1 as int) }
}

pub struct KeyedMessageFormat {
    pub pair_fmt: UniformPairMarshal<IntFormat::<u64>, IntFormat::<u64>>,
}

impl KeyedMessageFormat {
    pub fn new() -> Self
    {
        KeyedMessageFormat{
            pair_fmt: UniformPairMarshal::new(IntFormat::new(), IntFormat::new()),
        }
    }
}

impl KeyedMessageFormat {
    pub open spec fn to_pair(value: KeyedMessage) -> (int, int)
        recommends value.message is Define
    {
        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { 0 },
        };
        (value.key.0 as int, message_data as int)
    }

    exec fn exec_to_pair(value: KeyedMessage) -> (pair: (u64, u64))
    requires value.message is Define,
    ensures Self::to_pair(value.deepv()) == pair.deepv(),
    {
        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { assert(false); 0 },
        };
        (value.key.0, message_data)
    }

    exec fn exec_from_pair(pair: (u64, u64)) -> (km: KeyedMessage)
    ensures ({
        &&& Self::to_pair(km.deepv()) == pair.deepv()
        &&& km.deepv() == KeyedMessage{ key: Key(pair.0), message: Message::Define{value: Value(pair.1)} }
    }),
    {
        KeyedMessage{ key: Key(pair.0), message: Message::Define{value: Value(pair.1)}}
    }
}
    
impl Marshal for KeyedMessageFormat {
    type DV = KeyedMessage;
    type U = KeyedMessage;

    open spec fn valid(&self) -> bool { true }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.pair_fmt.parsable(data)
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let pair = self.pair_fmt.parse(data);
        KeyedMessage{ key: Key(pair.0 as u64), message: Message::Define{value: Value(pair.1 as u64)} }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        match self.pair_fmt.try_parse(slice, data) {
            None => None,
            Some(pair) => {
                let v = Self::exec_from_pair(pair);
                assert( Self::to_pair(v.deepv()) == pair.deepv() );
                assert( v.deepv() == self.parse(slice@.i(data@)) );
                Some(v)
            },
        }
    }

    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        self.pair_fmt.marshallable(Self::to_pair(value))
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        self.pair_fmt.spec_size(Self::to_pair(value))
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { assume(false); 0 },
        };
        let pair = (value.key.0, message_data);

        self.pair_fmt.exec_size(&pair)
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { assume(false); 0 },
        };
        let pair = (value.key.0, message_data);
        self.pair_fmt.exec_marshall(&pair, data, start)
    }
}

impl UniformSized for KeyedMessageFormat {
    open spec fn uniform_size(&self) -> (sz: usize) {
        (u64::uniform_size() + u64::uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self)
    ensures 0 < self.uniform_size()
    { }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    ensures sz == self.uniform_size()
    {
        u64::exec_uniform_size() + u64::exec_uniform_size()
    }
}

} //verus!
