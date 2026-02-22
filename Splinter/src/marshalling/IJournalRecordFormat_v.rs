// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::IntegerMarshalling_v::{IntFormat, IntFormattable};
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::marshalling::Wrappable_v::{Wrappable, WrappableFormat};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::implementation::JournalTypes_v::ILsn;
use crate::marshalling::WF_v::WF;
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::IAddress;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::journal::LinkedJournal_v::JournalRecord;

verus! {

// Since we only ever read journal pages sequentially, we'll use bulk marshalling instead of
// incremental seq accessors.
#[verifier::ext_equal]
pub struct JournalHeader {
    pub prior_rec: Pointer,
    pub start_lsn: LSN,
}

#[derive(Clone, Copy)]
#[verifier::ext_equal]
pub struct IJournalHeader {
    pub prior_rec: Option<IAddress>,
    pub start_lsn: ILsn,
}

impl WF for IJournalHeader {}
impl Parsedview<JournalHeader> for IJournalHeader {
    open spec fn parsedv(&self) -> JournalHeader {
        JournalHeader{
            prior_rec: match self.prior_rec {
                None => None,
                Some(iaddr) => Some(iaddr@),
            },
            start_lsn: self.start_lsn@ as nat,
        }
    }
}

#[verifier::ext_equal]
pub struct AJournalRecord {
    pub header: JournalHeader,
    pub messages: Seq<KeyedMessage>,
}

impl View for AJournalRecord {
    type V = JournalRecord;
    open spec fn view(&self) -> Self::V
    {
        let bdy = self.header.start_lsn;
        let seq_end = bdy + self.messages.len();

        JournalRecord{
            message_seq: MsgHistory{
                msgs: Map::new(|lsn: nat| bdy <= lsn < seq_end, |lsn: nat| self.messages[lsn-bdy]),
                seq_start: bdy, 
                seq_end: seq_end,
            },
            prior_rec: self.header.prior_rec,
        }
    }
}

#[verifier::ext_equal]
pub struct IJournalRecord {
    pub header: IJournalHeader,
    pub messages: Vec<KeyedMessage>,
}

impl WF for IJournalRecord {}
impl Parsedview<AJournalRecord> for IJournalRecord {
    open spec fn parsedv(&self) -> AJournalRecord {
        AJournalRecord{
            header: self.header.parsedv(),
            messages: self.messages@,
        }
    }
}

pub struct IJournalHeaderWrappable {}
impl Wrappable for IJournalHeaderWrappable {
    type AF = OptionFormat<IAddressFormat>;
    type BF = IntFormat<ILsn>;
    type DV = JournalHeader;
    type U = IJournalHeader;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        true
    }

    open spec fn to_pair(value: Self::DV) -> (Pointer, int)
    {
        (value.prior_rec, value.start_lsn as int)
    }

    open spec fn from_pair(pair: (Pointer, int)) -> (value: Self::DV)
    {
        Self::DV{ prior_rec: pair.0, start_lsn: pair.1 as nat }
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &Self::U) -> (pair: (Option<IAddress>, ILsn))
    {
        let pair = (value.prior_rec, value.start_lsn);
        assert( Self::to_pair((*value).parsedv()) == Parsedview::<(Pointer,int)>::parsedv(&pair) );  // verus #1534
        assume( pair.wf() );    // TODO(jonh) need to plumb an obligation through the trait? Maybe a custom pair type?
        pair
    }

    exec fn exec_from_pair(pair: (Option<IAddress>, ILsn)) -> (u: Self::U)
    {
        let u = Self::U{ prior_rec: pair.0, start_lsn: pair.1 };
//         assert( u.parsedv() == Self::from_pair(pair.parsedv()) );
        u
    }

    open spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    {
        (
            OptionFormat::<IAddressFormat>::spec_new(IAddressFormat::spec_new()),
            IntFormat::<ILsn>::spec_new())
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        let a_fmt = OptionFormat::<IAddressFormat>::new(IAddressFormat::new());
        let b_fmt = IntFormat::<ILsn>::new();

        assert( a_fmt.uniform_size() == 9 );
//         assert( b_fmt.uniform_size() == 4 );
        assert( a_fmt.uniform_size() as int + a_fmt.uniform_size() as int <= usize::MAX );
        (a_fmt, b_fmt)
    }
}

pub struct IJournalRecordWrappable {}
impl Wrappable for IJournalRecordWrappable {
    type AF = WrappableFormat<IJournalHeaderWrappable>;
    type BF = ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>;
    type DV = AJournalRecord;
    type U = IJournalRecord;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        true
    }

    open spec fn to_pair(value: Self::DV) -> (JournalHeader, Seq<KeyedMessage>)
    {
        (value.header, value.messages)
    }

    open spec fn from_pair(pair: (JournalHeader, Seq<KeyedMessage>)) -> (value: Self::DV)
    {
        Self::DV{ header: pair.0, messages: pair.1 }
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &Self::U) -> (pair: (IJournalHeader, Vec<KeyedMessage>))
    {
        // TODO(jonh) clonity clone clone
        let header_clone = value.header.clone();
        let messages_clone = value.messages.clone();
        let pair = (header_clone, messages_clone);
        assume( header_clone == value.header );
        assume( messages_clone == value.messages );
        assert( Self::to_pair((*value).parsedv()) == Parsedview::<(JournalHeader, Seq<KeyedMessage>)>::parsedv(&pair) );  // verus #1534
        assume( pair.wf() );    // TODO(jonh) need to plumb an obligation through the trait? Maybe a custom pair type?
        pair
    }

    exec fn exec_from_pair(pair: (IJournalHeader, Vec<KeyedMessage>)) -> (u: Self::U)
    {
        assert(pair.wf());
        let u = Self::U{ header: pair.0, messages: pair.1 };
        assert( u.parsedv() == Self::from_pair(pair.parsedv()) );   // manually  trigger trait ensures extn
        assert(u.wf());
        u
    }

    open spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    {
        (
            WrappableFormat::<IJournalHeaderWrappable>::spec_new(),
            Self::BF::spec_new(KeyedMessageFormat::spec_new(), IntFormat::<u8>::spec_new(), 200))
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        let a_fmt = WrappableFormat::<IJournalHeaderWrappable>::new();
        let b_fmt = Self::BF::new(KeyedMessageFormat::new(), IntFormat::<u8>::new(), 200);

        assert( a_fmt.uniform_size() == 17 );
        assert( b_fmt.uniform_size() == 200 );
        assert( a_fmt.uniform_size() as int + a_fmt.uniform_size() as int <= usize::MAX );
        (a_fmt, b_fmt)
    }
}

pub type IJournalRecordFormat = WrappableFormat<IJournalRecordWrappable>;

} //verus!
