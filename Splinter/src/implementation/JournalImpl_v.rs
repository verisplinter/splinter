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

verus!{

pub type LsnAddrIndexImpl = HashMapWithView<u64, IAddress>;

#[derive(Debug, Copy, Clone)]
pub struct JournalSnapshot {
    pub boundary_lsn: u64,
    pub freshest_rec: Option<IAddress>,
}

pub open spec fn iaddr_view(ptr: Option<IAddress>) -> Option<Address>
{
    match ptr {
        None => None,
        Some(iaddr) => Some(iaddr@),
    }
}

impl View for JournalSnapshot {
    type V = CachedJournal_v::JournalSnapShot;

    open spec fn view(&self) -> Self::V {
        Self::V{
            boundary_lsn: self.boundary_lsn as LSN,
            freshest_rec: iaddr_view(self.freshest_rec),
        }
    }
}

impl Parsedview<CachedJournal_v::JournalSnapShot> for JournalSnapshot {
    open spec fn parsedv(&self) -> CachedJournal_v::JournalSnapShot
    {
        self@
    }
}

pub struct JournalStatus {
    pub unmarshalled_tail: Vec<(Key,Value)>,
    pub lsn_addr_index: LsnAddrIndexImpl,
}

pub struct JournalImpl {
    snapshot: JournalSnapshot,
    status: Option<JournalStatus>,
}

impl JournalImpl {
    pub open spec fn wf(&self) -> bool {
        true
    }

    pub open spec fn seq_start(&self) -> LSN {
        0
    }

    pub exec fn exec_seq_start(&self) -> (out: u64)
    ensures out == self.seq_start()
    {
        0
    }

    pub open spec fn seq_end(&self) -> LSN {
        0
    }

    pub exec fn exec_seq_end(&self) -> (out: u64)
    ensures out == self.seq_end()
    {
        0
    }

    pub exec fn new(snapshot: JournalSnapshot) -> (out: Self)
//         TODO how do I express this? transition!s work, but not init!
//     ensures CachedJournal::initialize(snapshot@)
    {
        Self{ snapshot, status: None }
    }

    pub exec fn insert(&mut self, key: Key, value: Value)
    ensures self.wf(), self@.wf()
    {
    }
}

impl View for JournalImpl {
    type V = CachedJournal::State;
    open spec fn view(&self) -> Self::V {
        arbitrary()
    }
}

}//verus!
