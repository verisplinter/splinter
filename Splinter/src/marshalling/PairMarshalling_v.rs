// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::implementation::VecMap_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Deepview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::StaticallySized_v::StaticallySized;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;

verus! {

type PairMarshallable {
    type AM: Marshal;
    type BM: Marshal;
    type U;
    type TV;

    proof fn viewify(av: AM.DV, bv: BM.DV) -> TV
    ;

    exec fn extract(&'a u: U) -> ('a a: AM.U, 'a b: BM.U)
    ;
}

pub struct PairMarshal<P: PairMarshallable> {
    pub l_fmt: P::LM,
    pub a_fmt: P::AM,
    pub b_fmt: P::BM,
}

impl<P: PairMarshallable> PairMarshal<P> {
    fn new(a_fmt: P::AM, b_fmt: P::BM) -> Self
    {
        PairMarshal{ a_fmt, b_fmt }
    }
}

impl<P: PairMarshallable> Marshal for PairMarshal<P> {
    type DV = P::TV;
    type U = P::U;

    open spec fn valid(&self) -> bool {
        &&& self.a_fmt.valid()
        &&& self.b_fmt.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        self.a_fmt::spec_size(
        u64::uniform_size() + u64::uniform_size() <= data.len()
    }

    open spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let bdy0 = u64::uniform_size() as int;
        let bdy1 = u64::uniform_size() as int + u64::uniform_size() as int;
        let key = Key(self.key_fmt.parse(data.subrange(0, bdy0)) as u64);
        let message_value = self.message_fmt.parse(data.subrange(bdy0, bdy1)) as u64;
        KeyedMessage{ key, message: Message::Define{value: Value(message_value)} }
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < u64::exec_uniform_size() + u64::exec_uniform_size() {
            // Not enough slice for the format
            None
        } else if data.len() < slice.end {
            // Not enough data for the slice
            None
        } else {
            let key_slice = slice.subslice(0, u64::exec_uniform_size());
            let key = Key(self.key_fmt.exec_parse(&key_slice, data));
            let message_slice = slice.subslice(u64::exec_uniform_size(), u64::exec_uniform_size() + u64::exec_uniform_size());
            let message_value = self.message_fmt.exec_parse(&message_slice, data);
            let keyed_message = KeyedMessage{ key, message: Message::Define{value: Value(message_value)} };
            proof {
                assert( keyed_message.deepv() == keyed_message );   // trigger
                // extn: subrange transitivity
                let bdy0 = u64::uniform_size() as int;
                let bdy1 = u64::uniform_size() as int + u64::uniform_size() as int;
                let idata = slice@.i(data@);
                assert( idata.subrange(0, bdy0) == key_slice@.i(data@) );   // extn
                assert( idata.subrange(bdy0, bdy1) == message_slice@.i(data@) );    // extn
                assert( keyed_message == self.parse(idata) );   // extn
            }
            Some(keyed_message)
        }
    }
    
    open spec fn marshallable(&self, value: Self::DV) -> bool
    {
        true
    }
        
    open spec fn spec_size(&self, value: Self::DV) -> usize
    {
        (u64::uniform_size() + u64::uniform_size()) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        u64::exec_uniform_size() + u64::exec_uniform_size()
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let kend = self.key_fmt.exec_marshall(&value.key.0, data, start);

        assert( self.key_fmt.parse(data@.subrange(start as int, kend as int)) == value.key.0 ); // TODO delete
        let ghost mid_data = data@;

        let message_data = match value.message {
            Message::Define{value: Value(v)} => v,
            Message::Update{delta: Delta(_)} => { assume(false); 0 },
        };
        let end = self.message_fmt.exec_marshall(&message_data, data, kend);
        proof {
            // extn: second exec_marshall didn't stomp first
            assert( mid_data.subrange(start as int, kend as int) == data@.subrange(start as int, kend as int) );

            // extn: subrange transitivity
            let bdy0 = u64::uniform_size() as int;
            let bdy1 = u64::uniform_size() as int + u64::uniform_size() as int;
            assert( data@.subrange(start as int, end as int).subrange(0, bdy0)
                    == data@.subrange(start as int, kend as int) ); // extn

            assert( data@.subrange(start as int, end as int).subrange(bdy0, bdy1)
                    == data@.subrange(kend as int, end as int) );
        }
        end
    }
}

}//verus!
