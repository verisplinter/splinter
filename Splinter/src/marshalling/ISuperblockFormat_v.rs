// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::marshalling::Marshalling_v::Deepview;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Wrappable_v::*;
use crate::marshalling::WF_v::WF;
use crate::marshalling::JournalFormat_v::*;
use crate::marshalling::KeyValueFormat_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::VecMap_v::*;

verus! {

impl Deepview<ASuperblock> for ISuperblock {
    open spec fn deepv(&self) -> ASuperblock {
        ASuperblock{
            journal: self.journal.deepv(),
            store: self.store@,
        }
    }
}

impl WF for ISuperblock {}

pub struct SuperblockJSWrappable {}
impl Wrappable for SuperblockJSWrappable {
    type AF = JournalFormat;
    type BF = ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>;
    type DV = ASuperblock;
    type U = ISuperblock;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        true
    }

    open spec fn to_pair(value: Self::DV) -> (AJournal, Seq<(Key,Value)>)
    {
        (value.journal, value.store)
    }

    open spec fn from_pair(pair: (AJournal, Seq<(Key,Value)>)) -> (value: Self::DV)
    {
        Self::DV{ journal: pair.0, store: pair.1 }
    }

    proof fn to_from_bijective()
    {
    }

    exec fn exec_to_pair(value: &Self::U) -> (pair: (Journal, Vec<(Key,Value)>))
    {
        // TODO(jonh) clonity clone clone
        let journal_clone = value.journal.clone();
        let store_clone = value.store.clone();
        let pair = (journal_clone, store_clone);
        // TODO(jonh): why aren't we getting a clone spec?
        assume( journal_clone == value.journal );
        assume( store_clone == value.store );
        assert( Self::to_pair((*value).deepv()) == pair.deepv() );  // verus #1534
        assume( pair.wf() );    // TODO(jonh)
        pair
    }

    exec fn exec_from_pair(pair: (Journal, Vec<(Key, Value)>)) -> (u: Self::U)
    {
        let u = Self::U{ journal: pair.0, store: pair.1 };
        assert( u.deepv().store == Self::from_pair(pair.deepv()).store );   // extn
//         assert( u.deepv() == Self::from_pair(pair.deepv()) );
        u
    }

    open spec fn spec_new_format_pair() -> (Self::AF, Self::BF)
    {
        (
            JournalFormat::spec_new(), // TODO where is this implemented!?
            Self::BF::spec_new(KeyValueFormat::spec_new(), IntFormat::<u8>::spec_new(), 200))
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (
            JournalFormat::new(), // TODO where is this implemented!?
            Self::BF::new(KeyValueFormat::new(), IntFormat::<u8>::new(), 200))
    }
}

pub type ISuperblockFormat = WrappableFormat<SuperblockJSWrappable>;

} //verus!
