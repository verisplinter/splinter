// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Marshalling_v::Deepview;
use crate::marshalling::IntegerMarshalling_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::marshalling::Wrappable_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::implementation::JournalTypes_v::*;

verus! {

// Move to KeyedMessage?
impl Deepview<KeyedMessage> for KeyedMessage {
    open spec fn deepv(&self) -> KeyedMessage { *self }
}

// Move to ResizableUniformSizedElementSeqFormat?
impl<T,L> UniformSized for ResizableUniformSizedElementSeqFormat<T,L>
where T: Marshal + UniformSized, L: IntFormattable
{
    open spec fn us_valid(&self) -> bool
    {
        0 < self.total_size
    }

    open spec fn uniform_size(&self) -> (sz: usize)
    {
        self.total_size
    }

    proof fn uniform_size_ensures(&self)
    ensures 0 < self.uniform_size()
    {
    }

    exec fn exec_uniform_size(&self) -> (sz: usize)
    ensures sz == self.uniform_size()
    {
        self.total_size
    }
}

const JOURNAL_CAPACITY: usize = 200;

pub struct JournalFormatWrappable {}
impl Wrappable for JournalFormatWrappable {
    type AF = ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>;
    type BF = IntFormat::<ILsn>;
    type DV = AJournal;
    type U = Journal;

    open spec fn value_marshallable(value: AJournal) -> bool
    {
        // self.b_fmt.marshallable(value.msg_history)
        &&& true
    }

    open spec fn to_pair(value: AJournal) -> (Seq<KeyedMessage>, int)
    {
        (value.msg_history, value.seq_start as int)
    }

    open spec fn from_pair(pair: (Seq<KeyedMessage>, int)) -> (value: AJournal)
    {
        AJournal{msg_history: pair.0, seq_start: pair.1 as u64}
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair<'a>(value: &'a Journal) -> (pair: (&'a Vec<KeyedMessage>, &'a ILsn))
    {
        (&value.msg_history, &value.seq_start)
    }

    exec fn exec_from_pair(pair: (Vec<KeyedMessage>, ILsn)) -> (j: Journal)
    {
        Journal{msg_history: pair.0, seq_start: pair.1}
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (
            ResizableUniformSizedElementSeqFormat::new(
                KeyedMessageFormat::new(), IntFormat::<u8>::new(), JOURNAL_CAPACITY),
            IntFormat::new()
        )
    }
}

pub type JournalFormat = WrappableFormat<JournalFormatWrappable>;

//
//pub struct JournalFormat {
//    ilsn_fmt: IntFormat::<ILsn>,
//    msg_history_fmt: ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>,
//}
//
//impl JournalFormat {
//    fn new() -> Self
//    {
//        JournalFormat{
//            ilsn_fmt: IntFormat::new(),
//            // TODO hardcoded total size
//            msg_history_fmt: ResizableUniformSizedElementSeqFormat::new(
//                KeyedMessageFormat::new(),
//                IntFormat::<u8>::new(),
//                200),
//        }
//    }
//}
//
//impl Marshal for JournalFormat {
//    type DV = AJournal;
//    type U = Journal;
//
//    closed spec fn valid(&self) -> bool {
//        self.msg_history_fmt.valid()
//    }
//
//    closed spec fn parsable(&self, data: Seq<u8>) -> bool
//    {
//        &&& ILsn::uniform_size() <= data.len()
//        &&& self.msg_history_fmt.parsable(
//            data.subrange(ILsn::uniform_size() as int, data.len() as int))
//    }
//
//    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
//    {
//        let bdy0 = ILsn::uniform_size() as int;
//        let bdy1 = data.len() as int;
//        let seq_start = self.ilsn_fmt.parse(data.subrange(0, bdy0)) as ILsn;
//        let msg_history = self.msg_history_fmt.parse(data.subrange(bdy0, bdy1));
//        AJournal{seq_start, msg_history}
//    }
//
//    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
//    {
//        if slice.len() < ILsn::exec_uniform_size() {
//            // Not enough slice for the format
//            None
//        } else if data.len() < slice.end {
//            // Not enough data for the slice
//            None
//        } else {
//            let seq_start_slice = slice.subslice(0, ILsn::exec_uniform_size());
//            let seq_start = self.ilsn_fmt.exec_parse(&seq_start_slice, data);
//            let skip = ILsn::exec_uniform_size();
//            let msg_history_slice = slice.subslice(skip, slice.len());
//            proof {
//                let ghost idata = slice@.i(data@);
//                assert( idata.subrange(ILsn::uniform_size() as int, idata.len() as int)
//                    == msg_history_slice@.i(data@) ); // extn
//            }
//            let msg_history = match self.msg_history_fmt.try_parse(&msg_history_slice, data) {
//                None => {
//                    return None;
//                }
//                Some(msg_history) => msg_history
//            };
//            let out = Journal{msg_history, seq_start};
//
//            proof {
//                // extn: subrange transitivity
//                let bdy0 = ILsn::uniform_size() as int;
//                let bdy1 = slice@.len() as int;
//                let idata = slice@.i(data@);
//                assert( idata.subrange(0, bdy0) == seq_start_slice@.i(data@) );   // extn
//                assert( seq_start == self.parse(idata).seq_start );
//                assert( idata.subrange(bdy0, bdy1) == msg_history_slice@.i(data@) );   // extn
//
////                 assert( msg_history.deepv() == self.msg_history_fmt.parse(msg_history_slice@.i(data@)) );
//                assert( msg_history@ == self.parse(idata).msg_history );    // Saw this flake once
//                assert( out.deepv() == self.parse(idata) );   // extn
//            }
//            Some(out)
//        }
//    }
//    
//    closed spec fn marshallable(&self, value: Self::DV) -> bool
//    {
//        &&& ILsn::uniform_size() + self.msg_history_fmt.spec_size(value.msg_history) <= usize::MAX 
//        &&& value.wf()
//        &&& self.msg_history_fmt.marshallable(value.msg_history)
//    }
//        
//    closed spec fn spec_size(&self, value: Self::DV) -> usize
//    {
//        (ILsn::uniform_size() + self.msg_history_fmt.spec_size(value.msg_history)) as usize
//    }
//
//    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
//    {
//        ILsn::exec_uniform_size() + self.msg_history_fmt.exec_size(&value.msg_history)
//    }
//
//    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
//    {
//        let send = self.ilsn_fmt.exec_marshall(&value.seq_start, data, start);
//
//        assert( self.ilsn_fmt.parse(data@.subrange(start as int, send as int)) == value.seq_start );
//        let ghost mid_data = data@;
//        let end = self.msg_history_fmt.exec_marshall(&value.msg_history, data, send);
//        proof {
//            // extn: second exec_marshall didn't stomp first
//            assert( mid_data.subrange(start as int, send as int) == data@.subrange(start as int, send as int) );
//
//            // extn: subrange transitivity
//            let bdy0 = ILsn::uniform_size() as int;
//            let bdy1 = (end - start) as int;
//            assert( data@.subrange(start as int, end as int).subrange(0, bdy0)
//                    == data@.subrange(start as int, send as int) ); // extn
//
//            assert( data@.subrange(start as int, end as int).subrange(bdy0, bdy1)
//                    == data@.subrange(send as int, end as int) );
//            assert( self.parse(data@.subrange(start as int, end as int)).seq_start == value.seq_start );
//            assert( self.parse(data@.subrange(start as int, end as int)).msg_history == value.msg_history@ );
//            assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
//        }
//        end
//    }
//    
//}

} //verus!
