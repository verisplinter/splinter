// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::implementation::JournalTypes_v::ILsn;
use crate::marshalling::NatFormat_v::NatFormat;
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::IAddress;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::Marshal;
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

proof fn i_journal_header_wf_proof(
    prior_rec: Option<IAddress>,
    start_lsn: ILsn,
    hdr: IJournalHeader,
)
    requires
        prior_rec.wf(),
        start_lsn.wf(),
        hdr.prior_rec == prior_rec,
        hdr.start_lsn == start_lsn,
    ensures
        hdr.wf(),
{
}

proof fn i_journal_header_postcondition_proof(
    fmt: &IJournalHeaderFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: Option<IAddress>,
    field2_slice: &Slice,
    field2_value: ILsn,
    result: IJournalHeader,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.prior_rec == field1_value,
        result.start_lsn == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<Pointer>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<nat>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
}

proof fn i_journal_record_wf_proof(
    header: IJournalHeader,
    messages: Vec<KeyedMessage>,
    rec: IJournalRecord,
)
    requires
        header.wf(),
        messages.wf(),
        rec.header == header,
        rec.messages == messages,
    ensures
        rec.wf(),
{
}

proof fn i_journal_record_postcondition_proof(
    fmt: &IJournalRecordFormat,
    slice: &Slice,
    data: &Vec<u8>,
    field1_slice: &Slice,
    field1_value: IJournalHeader,
    field2_slice: &Slice,
    field2_value: Vec<KeyedMessage>,
    result: IJournalRecord,
)
    requires
        fmt.valid(),
        slice@.valid(data@),
        result.header == field1_value,
        result.messages == field2_value,
        field1_value.wf(),
        field2_value.wf(),
        fmt.parsable(slice@.i(data@)),
        Parsedview::<JournalHeader>::parsedv(&field1_value) == fmt.field1_fmt.parse(field1_slice@.i(data@)),
        Parsedview::<Seq<KeyedMessage>>::parsedv(&field2_value) == fmt.field2_fmt.parse(field2_slice@.i(data@)),
        field1_slice@.i(data@) == slice@.i(data@).subrange(0, fmt.field1_fmt.uniform_size() as int),
        field2_slice@.i(data@) == slice@.i(data@).subrange(
            fmt.field1_fmt.uniform_size() as int,
            fmt.field1_fmt.uniform_size() as int + fmt.field2_fmt.uniform_size() as int),
    ensures
        result.parsedv() == fmt.parse(slice@.i(data@)),
        result.wf(),
{
    assert(field2_value@ =~= Parsedview::<Seq<KeyedMessage>>::parsedv(&field2_value)); // trigger
}

} //verus!

struct_marshaller_2! {
    format_name: IJournalHeaderFormat,
    impl_type: IJournalHeader,
    spec_type: JournalHeader,
    wf_proof: i_journal_header_wf_proof,
    postcondition_proof: i_journal_header_postcondition_proof,
    field1: {
        impl_field: prior_rec,
        spec_field: prior_rec,
        formatter_type: OptionFormat<IAddressFormat>,
        formatter_spec_new: OptionFormat::spec_new(IAddressFormat::spec_new()),
        formatter_new: OptionFormat::new(IAddressFormat::new()),
    },
    field2: {
        impl_field: start_lsn,
        spec_field: start_lsn,
        formatter_type: NatFormat<u64>,
        formatter_spec_new: NatFormat::spec_new(),
        formatter_new: NatFormat::new(),
    }
}

struct_marshaller_2! {
    format_name: IJournalRecordFormat,
    impl_type: IJournalRecord,
    spec_type: AJournalRecord,
    wf_proof: i_journal_record_wf_proof,
    postcondition_proof: i_journal_record_postcondition_proof,
    field1: {
        impl_field: header,
        spec_field: header,
        formatter_type: IJournalHeaderFormat,
        formatter_spec_new: IJournalHeaderFormat::spec_new(),
        formatter_new: IJournalHeaderFormat::new(),
    },
    field2: {
        impl_field: messages,
        spec_field: messages,
        formatter_type: ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>,
        formatter_spec_new: ResizableUniformSizedElementSeqFormat::spec_new(KeyedMessageFormat::spec_new(), IntFormat::<u8>::spec_new(), 200),
        formatter_new: ResizableUniformSizedElementSeqFormat::new(KeyedMessageFormat::new(), IntFormat::<u8>::new(), 200),
    }
}

pub type JournalHeaderFmt = IJournalHeaderFormat;
pub type JournalPageFmt = IJournalRecordFormat;
