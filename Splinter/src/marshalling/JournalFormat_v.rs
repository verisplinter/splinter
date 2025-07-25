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
use crate::marshalling::WF_v::WF;

verus! {

// Move to KeyedMessage?
impl Deepview<KeyedMessage> for KeyedMessage {
    open spec fn deepv(&self) -> KeyedMessage { *self }
}

impl WF for Journal { }

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

    exec fn exec_to_pair(value: &Journal) -> (pair: (Vec<KeyedMessage>, ILsn))
    {
        // TODO(jonh): we don't want to clone, but I spent a couple hours trying
        // to figure out how to elegantly get references where they need to go,
        // and I failed. May need to rearrange how the Wrappable trait works to
        // keep the pair construction higher in the call graph.
        let mhclone = value.msg_history.clone();
        assume( mhclone == value.msg_history ); // TODO: hmm, Verus can't see the equality from clone?
        let pair = (mhclone, value.seq_start);
        assert( Self::to_pair(value.deepv()).0 == pair.deepv().0 ); // extn
        pair
    }

    exec fn exec_from_pair(pair: (Vec<KeyedMessage>, ILsn)) -> (j: Journal)
    {
        let j = Journal{msg_history: pair.0, seq_start: pair.1};
        assert( j.deepv().msg_history == pair.0.deepv() );  // extn
        j
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

} //verus!
