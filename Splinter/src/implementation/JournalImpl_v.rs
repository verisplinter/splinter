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
use crate::implementation::CacheImpl_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;

verus!{

// TODO: this file uses u64 a bunch where we should say ILsn to capture intent

// This is a silly index implementation, since it has an entry for every LSN :v)
pub type LsnAddrIndexImpl = HashMapWithView<u64, IAddress>;

pub open spec fn LsnAddrIndexImpl_view(selff: LsnAddrIndexImpl) -> LsnAddrIndex
{
    Map::new(|k: LSN| selff@.contains_key(k as u64), |k| selff@[k as u64]@)
}

exec fn index_assign_lsns(selff: &mut LsnAddrIndexImpl, low_inclusive: ILsn, high_exclusive: ILsn, addr: IAddress)
{
}

#[derive(Debug, Copy, Clone)]
pub struct JournalSnapshot {
    pub boundary_lsn: u64,
    pub freshest_rec: Option<IAddress>,
}

impl JournalSnapshot {
    pub open spec fn spec_new_empty(at_lsn: u64) -> Self {
        JournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None }
    }

    pub exec fn new_empty(at_lsn: u64) -> (out: Self)
        ensures out == Self::spec_new_empty(at_lsn)
    {
        JournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None }
    }
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

use crate::marshalling::WF_v::WF;

impl WF for JournalSnapshot {}

pub struct JournalStatus {
    pub unmarshalled_tail: Vec<(Key,Value)>,
    pub lsn_addr_index: LsnAddrIndexImpl,
    pub unmarshalled_tail_start: ILsn,   // invariant to agree with freshest_rec contents / boundary_lsn
}

impl JournalStatus {
    spec fn wf(&self) -> bool
    {
        true
    }

    exec fn new(tail_start: ILsn) -> (out: Self)
    ensures
        out.wf(),
        out.unmarshalled_tail_start == tail_start,
    {
        Self{
            unmarshalled_tail: vec![],
            lsn_addr_index: LsnAddrIndexImpl::new(),
            unmarshalled_tail_start: tail_start,
        }
    }

    closed spec fn tail_as_history(&self) -> MsgHistory
    {
        AJournal {
            msg_history: self.unmarshalled_tail@.map_values(|pr: (Key, Value)| KeyedMessage::from_kv(pr.0, pr.1)),
            seq_start: self.unmarshalled_tail_start,
        }@
    }
}

impl View for JournalStatus {
    type V = CachedJournal_v::JournalStatus;
    closed spec fn view(&self) -> Self::V {
        Self::V {
            unmarshalled_tail: self.tail_as_history(),
            lsn_addr_index: LsnAddrIndexImpl_view(self.lsn_addr_index),
        }
    }
}

pub struct IndexBuilder {
    next_head: JournalSnapshot,
}

pub struct JournalImpl {
    snapshot: JournalSnapshot,
    index_builder: Option<IndexBuilder>,
    status: Option<JournalStatus>,
    fmt: IJournalRecordFormat,
}

impl JournalImpl {
    pub closed spec fn wf(&self) -> bool {
        &&& self.fmt.valid()
        &&& match self.status {
            None => {
                self.index_builder is Some
            },
            Some(status) => {
                self.snapshot.boundary_lsn <= status.unmarshalled_tail_start
            }
        }
    }

    // TODO this must be a placeholder, right? Tell me this is a placeholder.
    pub closed spec fn seq_start(&self) -> LSN {
        0
    }

    pub exec fn exec_seq_start(&self) -> (out: u64)
    ensures out == self.seq_start()
    {
        0
    }

    pub closed spec fn index_ready(&self) -> bool
    {
        self.status is Some
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

    // TODO(delete): dead code
//     pub exec fn new_empty(at_lsn: u64) -> (out: Self)
//     ensures
//         out.wf(),
//         !out.index_ready(),
//         out@.snapshot == JournalSnapshot::spec_new_empty(at_lsn)@,
//     {
//         Self::new(JournalSnapshot::new_empty(at_lsn))
//     }

    pub exec fn new(snapshot: JournalSnapshot) -> (out: Self)
    ensures
        out.wf(),
        !out.index_ready(),
        out@.snapshot == snapshot@,
//         TODO how do I express this? transition!s work, but not init!
//     ensures CachedJournal::initialize(snapshot@)
    {
        Self{
            snapshot,
            index_builder: Some(IndexBuilder{
                next_head: snapshot,
            }),
            status: None,
            fmt: IJournalRecordFormat::new(),
        }
    }

    // This should do some cache reads and either bump another cache read (to walk the skip list)
    // or report that it's done (and the index is ready).
    // This could be a while loop that restarts from the beginning after every block for cache IO,
    // but that's quadratric compute, and will eventually suck. I'm going to write it keeping
    // intermediate state. That state will need an invariant wrt the cache, which Implementation
    // will have to hang onto for us, unfortunately.
    pub exec fn recover_index_step(&mut self, cache: &mut CacheImpl) -> (progress_ready: (bool, bool))
    requires
        old(self).wf(),
        !old(self).index_ready(),
        old(cache).inv(),
    ensures
        self.wf(),
        self@.wf(),
        cache.inv(),
        progress_ready.1 <==> self.index_ready(),
    {
        let mut progress = false;
        let mut ready = false;
        // swappery to deal with lack of &mut
        let mut index_builder = self.index_builder.take();
//         let mut dummy: Option<IndexBuilder> = None;
//         core::mem::swap(&mut self.index_builder, &mut dummy);
        index_builder = match index_builder {
            None => { assert(false); None }, // !index_ready && wf ==> we have an index_builder.
            Some(mut builder) => {
                match builder.next_head.freshest_rec {
                    None => {
                        // We got to the end of the journal linked list! We're done!
                        self.status = Some(JournalStatus::new(builder.next_head.boundary_lsn));
                        assert( self.snapshot.boundary_lsn <= self.status.unwrap().unmarshalled_tail_start ) by {
                            assume( false ); // This needs to become an invariant of the builder process.
                        }

                        // Build the index all at once at the end in a while loop. We just know
                        // (liveness fingers crossed) it's not going to have to pause for IO.
//                         index: LsnAddrIndexImpl,

                        // let the dummy object die, leaving the None in its place.
                        progress = true;
                        ready = true;
                        None
                    },
                    Some(addr) => {
                        // Can we read the next page from the cache?
                        match cache.read_or_fetch(&addr) {
                            None => {
                                // Cache is going to do a fetch and call us later. Bail out.
                                // Re-construct the struct
                                Some(builder)
                            },
                            Some(raw_page) => {
                                // Parse the page
                                let all_slice = Slice::all(raw_page.borrow());
                                assert( all_slice@.i(raw_page.value()) == raw_page.value() );
                                assert( self.fmt.parsable(all_slice@.i(raw_page.value())) ) by {
                                    assume( false ); // system invariant
                                }
                                let i_journal_record = self.fmt.exec_parse(&all_slice, raw_page.borrow());
                                
                                // Advance the pointer.
                                builder.next_head.freshest_rec = i_journal_record.header.prior_rec;

                                // Another invocation will do useful work without waiting for IO.
                                progress = true;
                                Some(builder)
                            },
                        }
                    },
                }
            }
        };
        core::mem::swap(&mut self.index_builder, &mut index_builder);
        assert( self.wf() );
        (progress, ready)
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
        self.index_ready(),
    {
        // swappery to deal with lack of &mut
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

    pub broadcast proof fn view_ensures(self)
        ensures self.index_ready() <==> (#[trigger] self@).status is Some
    {
    }

    pub fn is_empty(&self) -> bool
    requires self.index_ready()
    {
        self.status.as_ref().unwrap().unmarshalled_tail.len() > 0 || self.snapshot.freshest_rec.is_some()
    }

    // Reveal snapshot for use in Implementation::send_superblock
    pub fn get_snapshot(&self) -> JournalSnapshot
    {
        self.snapshot.clone()
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
