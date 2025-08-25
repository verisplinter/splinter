// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
// use vstd::std_specs::hash::*;
// use crate::spec::MapSpec_t::*;
// use crate::spec::AsyncDisk_t::*;
// use crate::spec::KeyType_t::*;
// use crate::spec::Messages_t::*;
// use crate::spec::TotalKMMap_t::*;
// use crate::spec::FloatingSeq_t::*;
// use crate::implementation::DiskLayout_v::*;
// use crate::marshalling::Marshalling_v::*;
// use crate::marshalling::IntegerMarshalling_v::*;
// use crate::marshalling::KVPairFormat_v::*;
// use crate::marshalling::Slice_v::*;
// use crate::marshalling::StaticallySized_v::*;
// use crate::marshalling::UniformSizedSeq_v::*;

verus! {

// impl Parsedview<Superblock> for ISuperblock {
//     open spec fn parsedv(&self) -> Superblock {
//         self@
//     }
// }
// 
// struct SuperblockKVTypes {
//     key_fmt: IntFormat<u64>,
//     value_fmt: IntFormat<u64>,
// }
// 
// impl SuperblockKVTypes {
//     exec fn new(
//         key_format: <Self as UniformSizedKVTrait>::UKeyFormat,
//         value_format: <Self as UniformSizedKVTrait>::UValueFormat) -> Self
//     {
//         Self {
//             key_fmt: key_format,
//             value_fmt: value_format,
//         }
//     }
// }
// 
// impl UniformSizedKVTrait for SuperblockKVTypes {
//     type UKeyFormat = IntFormat<u64>;
//     type UValueFormat = IntFormat<u64>;
// 
//     exec fn key_format(&self) -> &Self::UKeyFormat
//     {
//         &self.key_fmt
//     }
// 
//     exec fn value_format(&self) -> &Self::UValueFormat
//     {
//         &self.value_fmt
//     }
// 
//     proof fn no_overflow(kf: &Self::UKeyFormat, vf: &Self::UValueFormat)
//     {}
// }
// 
// type VersionType = u64;
// 
// pub struct SuperblockFormat {
//     version_format: IntFormat<VersionType>,
//     kvpair_format: UniformSizedElementSeqFormat<KVPairFormat<SuperblockKVTypes>>,
// }
// 
// impl SuperblockFormat {
//     spec fn get_kvpair_slice(&self, data: Seq<u8>) -> SpecSlice
//     {
//         SpecSlice{ start: VersionType::uniform_size() as int, end: data.len() as int }
//     }
// 
//     exec fn exec_get_kvpair_slice(&self, slice: &Slice, data: &Vec<u8>) -> (out: Slice)
//     requires
//         slice@.valid(data@),
//         VersionType::uniform_size() <= slice@.len(),
//     ensures
//         out@.valid(data@),
//         out@.i(data@) == self.get_kvpair_slice(slice@.i(data@)).i(slice@.i(data@)),
//     {
//         let out = slice.xslice(&Slice{ start: VersionType::exec_uniform_size(), end: slice.len() });
//         // extn trigger failure
//         assert( out@.i(data@) == self.get_kvpair_slice(slice@.i(data@)).i(slice@.i(data@)) );
//         out
//     }
// 
//     exec fn vec_kvpair_as_hashmap(v: Vec<KVPair<SuperblockKVTypes>>) -> HashMapWithView<Key, Value>
//     {
//         assume( obeys_key_model::<Key>() );
//         HashMapWithView::new()
//     }
// }
// 
// impl Marshal for SuperblockFormat {
//     type DV = Superblock;
//     type U = ISuperblock;
// 
//     closed spec fn valid(&self) -> bool
//     {
//         &&& self.version_format.valid()
//         &&& self.kvpair_format.valid()
//     }
// 
//     //////////////////////////////////////////////////////////////////////
//     // Parsing
//     //////////////////////////////////////////////////////////////////////
// 
//     closed spec fn parsable(&self, data: Seq<u8>) -> bool
//     {
//         &&& self.version_format.parsable(data)
//         &&& self.kvpair_format.parsable(self.get_kvpair_slice(data).i(data))
//     }
// 
//     closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
//     {
//         let store_pairs = self.kvpair_format.parse(self.get_kvpair_slice(data).i(data));
//         let store = PersistentState{ appv: MapSpec::State{ kmmap: TotalKMMap::empty()}};    // the lie
//         let version_index = self.version_format.parse(data) as nat;
//         Superblock{ store, version_index }
//     }
// 
//     exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
//     {
//         if slice.len() < VersionType::exec_uniform_size() {
//             return None
//         }
// 
//         let kvdata = self.kvpair_format.try_parse(&self.exec_get_kvpair_slice(slice, data), data);
//         if kvdata.is_none() {
//             return None
//         }
// 
//         let version_index = self.version_format.exec_parse(slice, data);
//         let sb = ISuperblock{ store: Self::vec_kvpair_as_hashmap(kvdata.unwrap()), version_index };
//         assume( sb.parsedv().store == self.parse(slice@.i(data@)).store ); // see parse().lie
//         assert( sb.parsedv() == self.parse(slice@.i(data@)) );
//         Some( sb )
//     }
// 
//     exec fn exec_parsable(&self, slice: &Slice, data: &Vec<u8>) -> (p: bool)
//     {
//         assume( false );
//         false
//     }
// 
//     exec fn exec_parse(&self, slice: &Slice, data: &Vec<u8>) -> (value: Self::U)
//     {
//         assume( false );
//         ISuperblock{
//             store: HashMapWithView::new(),
//             version_index: 0
//         }
//     }
// 
//     //////////////////////////////////////////////////////////////////////
//     // Marshalling
//     //////////////////////////////////////////////////////////////////////
// 
//     closed spec fn marshallable(&self, value: Self::DV) -> bool
//     {
//         true
//     }
// 
//     closed spec fn spec_size(&self, value: Self::DV) -> usize
//     {
//         19
//     }
// 
//     exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
//     {
//         assume( false );
//         19
//     }
// 
//     exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     {
//         assume( false );
//         19
//     }
// }

}
