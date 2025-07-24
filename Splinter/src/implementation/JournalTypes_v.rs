// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Deepview;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;

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
        forall |i| #![auto] 0 <= i < self.msg_history.len() ==> self.msg_history[i].message is Define
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

// The deepview only takes us up to AJournal, so that the marshalling spec fns talk
// about Seq<KeyedMessage>, not the Map-shaped MsgHistory object.
impl Deepview<AJournal> for Journal {
    open spec fn deepv(&self) -> AJournal {
        AJournal{msg_history: self.msg_history@, seq_start: self.seq_start}
    }
}

pub struct Journal {
    pub msg_history: Vec<KeyedMessage>,
    pub seq_start: ILsn,
}

impl View for Journal {
    type V = MsgHistory;

    open spec fn view(&self) -> Self::V
    {
        self.deepv()@
    }
}

struct JournalFormat {
    ilsn_fmt: IntFormat::<ILsn>,
    msg_history_fmt: ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>,
}

} //verus!
