// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::marshalling::Marshalling_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Wrappable_v::*;
use crate::marshalling::WF_v::WF;
use crate::marshalling::JournalSnapshotFormat_v::*;
use crate::marshalling::KeyValueFormat_v::*;
use crate::marshalling::UniformSized_v::*;
use crate::marshalling::PaddedFormat_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::JournalSnapshotFormat_v::JournalSnapshotFormat;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::CachedJournal_v;
use crate::implementation::JournalImpl_v::JournalSnapshot;
use crate::disk::GenericDisk_v::Address;
use crate::disk::GenericDisk_v::IAddress;

verus! {

pub struct SuperblockJSWrappable {}
impl Wrappable for SuperblockJSWrappable {
    type AF = JournalSnapshotFormat;
    type BF = ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>;
    type DV = ASuperblock;
    type U = ISuperblock;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        true
    }

    open spec fn to_pair(value: Self::DV) -> (CachedJournal_v::JournalSnapShot, Seq<(Key,Value)>)
    {
        (value.journal, value.store)
    }

    open spec fn from_pair(pair: (CachedJournal_v::JournalSnapShot, Seq<(Key,Value)>)) -> (value: Self::DV)
    {
        Self::DV{ journal: pair.0, store: pair.1 }
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &Self::U) -> (pair: (JournalSnapshot, Vec<(Key,Value)>))
    {
        // TODO(jonh) clonity clone clone
        let journal_snapshot_clone = value.journal_snapshot.clone();
        let store_clone = value.store.clone();
        let pair = (journal_snapshot_clone, store_clone);
        assume( journal_snapshot_clone == value.journal_snapshot );
        assume( store_clone == value.store );
        assert( Self::to_pair((*value).parsedv()) == pair.parsedv() );  // verus #1534
        assume( pair.wf() );    // TODO(jonh) need to plumb an obligation through the trait? Maybe a custom pair type?
        pair
    }

    exec fn exec_from_pair(pair: (JournalSnapshot, Vec<(Key, Value)>)) -> (u: Self::U)
    {
        let u = Self::U{ journal_snapshot: pair.0, store: pair.1 };
        assert( u.parsedv().store == Self::from_pair(pair.parsedv()).store );   // extn
//         assert( u.parsedv() == Self::from_pair(pair.parsedv()) );
        u
    }

    open spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    {
        (
            JournalSnapshotFormat::spec_new(),
            Self::BF::spec_new(KeyValueFormat::spec_new(), IntFormat::<u8>::spec_new(), 200))
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        let a_fmt = JournalSnapshotFormat::new();
        let b_fmt = Self::BF::new(KeyValueFormat::new(), IntFormat::<u8>::new(), 200);

        assert( a_fmt.uniform_size() == a_fmt.pair_fmt.a_fmt.uniform_size() + a_fmt.pair_fmt.b_fmt.uniform_size() );

        use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
        
        assert( a_fmt.pair_fmt.a_fmt.uniform_size() == 8 );
        assert( a_fmt.pair_fmt.b_fmt.uniform_size() == 9 );
        assert( b_fmt.uniform_size() == 200 );
        assert( a_fmt.uniform_size() as int + a_fmt.uniform_size() as int <= usize::MAX );
        (a_fmt, b_fmt)
    }
}

pub type ISuperblockFormat = PaddedFormat<WrappableFormat<SuperblockJSWrappable>>;

impl ISuperblockFormat {
    pub open spec fn spec_new() -> (out: Self)
    {
        PaddedFormat{
            format: WrappableFormat::<SuperblockJSWrappable>::spec_new(),
            pad_size: BLOCK_SIZE
        }
    }

    pub fn new() -> (out: Self)
    ensures out == Self::spec_new()
    {
        PaddedFormat{
            format: WrappableFormat::<SuperblockJSWrappable>::new(),
            pad_size: BLOCK_SIZE
        }
    }
}

} //verus!
