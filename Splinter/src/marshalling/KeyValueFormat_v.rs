// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
// use crate::abstract_system::MsgHistory_v::KeyedMessage;
// use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::Deepview;
// use crate::marshalling::Marshalling_v::{Marshal, Deepview};
// use crate::marshalling::IntegerMarshalling_v::IntFormat;
// use crate::marshalling::StaticallySized_v::StaticallySized;
// use crate::marshalling::UniformSized_v::UniformSized;
// use crate::marshalling::UniformPairFormat_v::UniformPairMarshal;

verus! {

impl Deepview<(Key,Value)> for (Key,Value) {
    open spec fn deepv(&self) -> (Key,Value) { (self.0, self.1) }
}

// pub struct KeyValueFormat {
//     pub pair_fmt: UniformPairMarshal<IntFormat::<u64>, IntFormat::<u64>>,
// }
// 
// impl KeyValueFormat {
//     fn new() -> Self
//     {
//         KeyValueFormat{
//             pair_fmt: UniformPairMarshal::new(IntFormat::new(), IntFormat::new()),
//         }
//     }
// }
// 
// impl Marshal for KeyValueFormat {
//     type DV = (Key, Value);
//     type U = (Key, Value);
// 
//     open spec fn valid(&self) -> bool { true }
// 
//     open spec fn parsable(&self, data: Seq<u8>) -> bool
//     {
//         self.pair_fmt.parsable(data)
//     }
// 
//     open spec fn parse(&self, data: Seq<u8>) -> Self::DV
//     {
//         let pair = self.pair_fmt.parse(data);
//         KeyedMessage{ key: pair.0, message: Message::Define{value: Value(pair.1)} }
//     }
// 
//     exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
//     {
//         match self.pair_fmt.try_parse(data) {
//             None => None,
//             Some(pair) => KeyedMessage{ key: pair.0, message: Message::Define{value: Value(pair.1)}},
//         }
//     }
//     
//     open spec fn marshallable(&self, value: Self::DV) -> bool
//     {
//         self.pair_fmt.marshallable(value)
//     }
//         
//     open spec fn spec_size(&self, value: Self::DV) -> usize
//     {
//         self.pair_fmt.spec_size(value)
//     }
// 
//     exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
//     {
//         self.pair_fmt.exec_size(value)
//     }
// 
//     exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     {
//         let message_data = match value.message {
//             Message::Define{value: Value(v)} => v,
//             Message::Update{delta: Delta(_)} => { assume(false); 0 },
//         };
//         let pair = (value.key.0, message_data);
//         self.pair_fmt.exec_marshall(&pair, data, start)
//     }
// }
// 
// impl UniformSized for KeyValueFormat {
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

} //verus!
