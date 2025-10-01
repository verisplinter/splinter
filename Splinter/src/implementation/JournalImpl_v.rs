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

verus!{

pub type LsnAddrIndexImpl = HashMapWithView<u64, IAddress>;

pub open spec fn LsnAddrIndexImpl_view(selff: LsnAddrIndexImpl) -> LsnAddrIndex
{
    Map::new(|k: LSN| selff@.contains_key(k as u64), |k| selff@[k as u64]@)
}

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
    pub unmarshalled_tail_start: ILsn,   // invariant to agree with freshest_rec contents / boundary_lsn
}

impl JournalStatus {
    pub closed spec fn tail_as_history(&self) -> MsgHistory
    {
        AJournal {
            msg_history: self.unmarshalled_tail@.map_values(|pr: (Key, Value)| KeyedMessage::from_kv(pr.0, pr.1)),
            seq_start: self.unmarshalled_tail_start,
        }@
    }
}

impl View for JournalStatus {
    type V = CachedJournal_v::JournalStatus;
    open spec fn view(&self) -> Self::V {
        Self::V {
            unmarshalled_tail: self.tail_as_history(),
            lsn_addr_index: LsnAddrIndexImpl_view(self.lsn_addr_index),
        }
    }
}

pub struct JournalImpl {
    snapshot: JournalSnapshot,

    // TODO(discuss with verus): I can't put JournalStatus behind an option, because then I can't
    // reach through the option with unwrap() or match Some(ref mut v); I get
    // "The verifier does not yet support the following Rust feature: &mut types, except in special
    // cases"
    // Evidently field access is an allowed special case. Is there a better way to do this?
    status: Option<JournalStatus>,
//     index_known: bool,
//     status: JournalStatus,
}

impl JournalImpl {
    pub closed spec fn wf(&self) -> bool {
        match self.status {
            None => true,
            Some(status) =>
                self.snapshot.boundary_lsn <= status.unmarshalled_tail_start,
        }
    }

    pub closed spec fn seq_start(&self) -> LSN {
        0
    }

    pub exec fn exec_seq_start(&self) -> (out: u64)
    ensures out == self.seq_start()
    {
        0
    }

    pub closed spec(checked) fn seq_end(&self) -> LSN
    recommends self.index_ready()
    {
        self.status.unwrap().tail_as_history().seq_end
    }

    pub exec fn exec_seq_end(&self) -> (out: u64)
    requires self.index_ready()
    ensures out == self.seq_end()
    {
        match &self.status {
            None => 0,
            Some(status) => {
                // this cheat is incurrent a runtime check, ugh
                if u64::MAX - status.unmarshalled_tail_start < status.unmarshalled_tail.len() as u64 {
                    convert_overflow_into_liveness_failure();
                }

                status.unmarshalled_tail_start + status.unmarshalled_tail.len() as u64
            }
        }
    }

    pub closed spec fn index_ready(&self) -> bool
    {
        self.status is Some
    }

    pub exec fn new(snapshot: JournalSnapshot) -> (out: Self)
//         TODO how do I express this? transition!s work, but not init!
//     ensures CachedJournal::initialize(snapshot@)
    {
        Self{ snapshot, status: None }
    }

    pub exec fn insert(&mut self, key: Key, value: Value)
    requires
        old(self).wf(),
        old(self).index_ready(),
    ensures
        self.wf(),
        self@.wf(),
        self.seq_start() == old(self).seq_start(),
        self.seq_end() == old(self).seq_end() + 1,
        CachedJournal_v::CachedJournal::State::put(old(self)@, self@,
            CachedJournal_v::CachedJournal::Label::Put{
            messages: MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value))
        }),
    {
        // Since we don't have &mut results in verus yet, we need to swap the
        // option out of self, deconstruct it, do the work we want on the inner struct,
        // then reassemble the option and swap it back in. 🫤
        let mut dummy: Option<JournalStatus> = None;
        core::mem::swap(&mut self.status, &mut dummy);
        dummy = match dummy {
            None => { None },
            Some(mut status) => {
                status.unmarshalled_tail.push((key,value));
                Some(status)
            }
        };
        core::mem::swap(&mut self.status, &mut dummy);

//         assert( old(self)@.seq_start() == self.snapshot.boundary_lsn );
//         assert( old(self)@.seq_end() == old(self)@.status.unwrap().unmarshalled_tail.seq_end );
//         assert( old(self)@.seq_end() == old(self).status.tail_as_history().seq_end );
// 
//         assert( old(self).snapshot.boundary_lsn <= old(self).status.unmarshalled_tail_start@ );
//         assert( old(self).status.unmarshalled_tail_start@ <= old(self).status.tail_as_history().seq_end );
// 
//         assert( old(self)@.seq_start() <= old(self)@.seq_end() );
//         assert( self@.seq_start() == old(self)@.seq_start() );
//         assert( self@.seq_end() == old(self)@.seq_end() + 1 );
//         assert( self@.seq_start() <= self@.seq_end() );
//         assert( self@.wf() );

        proof {
            let messages = MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value));
            let old_tail = old(self)@.status.unwrap().unmarshalled_tail;
            let new_tail = self@.status.unwrap().unmarshalled_tail;
            assert( old_tail.seq_end == old(self).status.unwrap().tail_as_history().seq_end );
            assert( old_tail.seq_end == old(self).seq_end() );
            assert( old_tail.can_concat(messages) );

            assert( new_tail == old_tail.concat(messages) );
            assert(
                CachedJournal_v::CachedJournal::State::put(old(self)@, self@,
                    CachedJournal_v::CachedJournal::Label::Put{
                    messages: MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value))
                })
            );
        }
    }
}

impl View for JournalImpl {
    type V = CachedJournal::State;
    closed spec fn view(&self) -> Self::V {
        CachedJournal_v::CachedJournal::State {
            snapshot: self.snapshot@,
            status: match self.status {
                None => None,
                Some(status) => Some(status@),
            }
        }
    }
}

}//verus!
