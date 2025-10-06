// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::hash_map::HashMapWithView;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::implementation::OverflowFiction_v::*;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::disk::GenericDisk_v::{Address, IAddress};
use crate::implementation::CachedJournal_v;
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::implementation::JournalModel_v::LsnAddrIndex;
use crate::spec::AsyncDisk_t::RawPage;

verus!{

pub struct CacheImpl {
}

impl CacheImpl {
    pub exec fn new() -> Self
    {
        unreached()
    }

    // Some => here's the page! Hooray! (borrow with lifetime?)
    // None => we've initiated the IO; try again later
    pub exec fn read_or_fetch(&self, addr: &IAddress) -> Option<Vec<u8>>
    {
        unreached()
    }
}

}//verus!
