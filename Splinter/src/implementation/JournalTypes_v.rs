// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::OverflowFiction_v::*;

verus! {

pub type ILsn = u64;

// An "abstract journal" is a hop between the impl Journal type and the abstract MsgHistory it
// represents.
pub struct AJournal {
    pub msg_history: Seq<KeyedMessage>,
    pub seq_start: ILsn,
}

impl AJournal {
    pub open spec fn wf(self) -> bool
    {
        &&& self.seq_start + self.msg_history.len() <= u64::MAX
        &&& forall |i| #![auto] 0 <= i < self.msg_history.len() ==> self.msg_history[i].message is Define
    }
}

impl View for AJournal
{
    type V = MsgHistory;

    open spec fn view(&self) -> Self::V
    {
        let seq_start = self.seq_start as nat;
        let seq_end = (self.msg_history.len() + seq_start) as nat;
        let msgs = Map::new(
            |k: LSN| seq_start <= k < seq_end,
            |k: LSN| self.msg_history[k - seq_start]
        );
        MsgHistory{msgs, seq_start, seq_end}
    }
}

// The parsedview only takes us up to AJournal, so that the marshalling spec fns talk
// about Seq<KeyedMessage>, not the Map-shaped MsgHistory object.
impl Parsedview<AJournal> for Journal {
    open spec fn parsedv(&self) -> AJournal {
        AJournal{msg_history: self.msg_history@, seq_start: self.seq_start}
    }
}

#[derive(Debug)]
pub struct Journal {
    pub msg_history: Vec<KeyedMessage>,
    pub seq_start: ILsn,
}

impl Journal {
    pub fn new_empty() -> (out: Self)
        ensures out@@.wf(), out@@.is_empty(), out.seq_start == 0
    {
        Journal{ msg_history: vec![], seq_start:0 }
    }

    pub fn seq_end(&self) -> (out: ILsn)
        requires self@.wf()
        ensures self@@.seq_end == out
    {
        let out = self.seq_start + self.msg_history.len() as u64;
        assert( self@@.seq_end == out );
        out
    }

    pub fn insert(&mut self, key: Key, value: Value)
        requires old(self)@.wf()
        ensures
            self@.wf(),
            self@@.seq_start == old(self)@@.seq_start,
            self@@.seq_end == old(self)@@.seq_end+1,
            self@@.msgs =~= old(self)@@.msgs.insert(old(self)@@.seq_end,
                KeyedMessage{key, message: Message::Define{value}}),
    {
        if self.seq_end() == u64::MAX {
            convert_overflow_into_liveness_failure();
        }
        self.msg_history.push(KeyedMessage{key, message: Message::Define{value}});
    }
}

impl View for Journal {
    type V = AJournal;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv()
    }
}

impl Clone for Journal {
    fn clone(&self) -> Self {
        Journal{
            msg_history: self.msg_history.clone(),
            seq_start: self.seq_start
        }
    }
}


struct JournalFormat {
    ilsn_fmt: IntFormat::<ILsn>,
    msg_history_fmt: ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>,
}

} //verus!
