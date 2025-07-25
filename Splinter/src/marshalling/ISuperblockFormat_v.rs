// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::marshalling::Marshalling_v::Deepview;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Wrappable_v::*;
use crate::marshalling::JournalFormat_v::*;
use crate::marshalling::KeyValueFormat_v::*;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::implementation::JournalTypes_v::*;
use crate::implementation::SuperblockTypes_v::*;

verus! {

impl Deepview<ASuperblock> for ISuperblock {
    open spec fn deepv(&self) -> ASuperblock {
        ASuperblock{journal: self.journal.deepv(), store: self.store.deepv()}
    }
}

pub struct SuperblockJSWrappable {}
impl Wrappable for SuperblockJSWrappable {
    type AF = JournalFormat;
    type BF = ResizableUniformSizedElementSeqFormat<KeyValueFormat, u8>;
    type DV = ASuperblock;
    type U = ISuperblock;

    open spec fn value_marshallable(value: Self::DV) -> bool
    {
        // We aren't gonna need Delta values for a long time
        value.message is Define
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
        let pair = (value.journal, value.store);
        assert( Self::to_pair((*value).deepv()) == pair.deepv() );  // verus #1534
        pair
    }

    exec fn exec_from_pair(pair: (Journal, Vec<(Key, Value)>)) -> (u: Self::U)
    {
        Self::DV{ journal: pair.0, store: pair.1 }
    }

    exec fn new_format_pair() -> (Self::AF, Self::BF)
    {
        (JournalFormat::new(), Self::BF::new())
    }
}

// WrappableFormat<SuperblockJSWrappable>

} //verus!
