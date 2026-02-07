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
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::AtomicState_v::to_journal_reads;
use crate::implementation::OverflowFiction_v::*;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer};
use crate::implementation::CachedJournal_v;
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::LsnAddrIndex;
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::IJournalRecordFormat_v::{IJournalRecord, IJournalRecordFormat};
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
pub struct IJournalSnapshot {
    pub boundary_lsn: u64,
    pub freshest_rec: Option<IAddress>,
}

impl IJournalSnapshot {
    pub open spec fn spec_new_empty(at_lsn: u64) -> Self {
        IJournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None }
    }

    pub exec fn new_empty(at_lsn: u64) -> (out: Self)
        ensures out == Self::spec_new_empty(at_lsn)
    {
        IJournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None }
    }
}

pub open spec fn iaddr_view(ptr: Option<IAddress>) -> Option<Address>
{
    match ptr {
        None => None,
        Some(iaddr) => Some(iaddr@),
    }
}


#[verifier::external_body]
fn please_panic()
    ensures false
{
    panic!();
}

impl View for IJournalSnapshot {
    type V = CachedJournal_v::JournalSnapshot;

    open spec fn view(&self) -> Self::V {
        Self::V{
            boundary_lsn: self.boundary_lsn as LSN,
            freshest_rec: iaddr_view(self.freshest_rec),
        }
    }
}

impl Parsedview<CachedJournal_v::JournalSnapshot> for IJournalSnapshot {
    open spec fn parsedv(&self) -> CachedJournal_v::JournalSnapshot
    {
        self@
    }
}

use crate::marshalling::WF_v::WF;

impl WF for IJournalSnapshot {}

pub struct FrozenJournal {
    pub snapshot: IJournalSnapshot,
    pub seq_end: ILsn,
}

impl FrozenJournal {
    pub open spec fn wf(self) -> bool {
        &&& self.seq_start() <= self.seq_end
        &&& self.snapshot.freshest_rec is None ==> self.seq_end == self.snapshot.boundary_lsn
        &&& self.snapshot.freshest_rec is Some ==> self.seq_start() < self.seq_end
    }

    pub open spec fn seq_start(self) -> ILsn { self.snapshot.boundary_lsn }
}

pub struct IJournalStatus {
    pub lsn_addr_index: LsnAddrIndexImpl,
    pub unmarshalled_tail: Vec<(Key,Value)>,
    pub unmarshalled_tail_start: ILsn,   // invariant to agree with freshest_rec contents / boundary_lsn
}

impl IJournalStatus {
    spec fn wf(&self) -> bool
    {
        // there should be no gap in between 
        true
    }

    closed spec fn tail_as_history(&self) -> MsgHistory
    {
        AJournal {
            msg_history: self.unmarshalled_tail@.map_values(|pr: (Key, Value)| KeyedMessage::from_kv(pr.0, pr.1)),
            seq_start: self.unmarshalled_tail_start,
        }@
    }
}

impl View for IJournalStatus {
    type V = CachedJournal_v::JournalStatus;
    closed spec fn view(&self) -> Self::V {
        Self::V {
            unmarshalled_tail: self.tail_as_history(),
            lsn_addr_index: LsnAddrIndexImpl_view(self.lsn_addr_index),
        }
    }
}

pub struct IndexBuilder {
    next_head: IJournalSnapshot,
}

pub enum RecoverIndexResult{
    CacheLoad{slot_handle: MutHandle, addr: IAddress},
    IndexComplete{reads: Ghost<Map<Address, RawPage>>},
    IndexProgress{},
}

pub struct JournalImpl {
    snapshot: IJournalSnapshot,
    index_builder: Option<IndexBuilder>,
    status: Option<IJournalStatus>,
    fmt: IJournalRecordFormat,
}

pub open spec fn load_index_labels(reads: Map<Address, RawPage>) -> (Cache::Label, CachedJournal::Label)
{
    let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let journal_lbl = CachedJournal::Label::LoadIndex{reads: to_journal_reads(reads)};
    (cache_lbl, journal_lbl)
}

impl IJournalRecord {
    exec fn seq_end(&self) -> (out: ILsn)
        requires self.wf()
        ensures out@ == self.parsedv().header.start_lsn + self.parsedv().messages.len()
    {
        assume(self.header.start_lsn + (self.messages.len() as u64) < u64::MAX);
        self.header.start_lsn + self.messages.len() as u64
    }

    exec fn cropped_prior(self, bdy: ILsn) -> (out: Option<IAddress>)
        requires self.wf()
        ensures ({
            let i_result = self.parsedv()@.cropped_prior(bdy as nat);
            &&& i_result is None ==> out is None
            &&& i_result is Some ==> i_result == Some(out.unwrap()@)
        })
    {
        if bdy < self.header.start_lsn { self.header.prior_rec } else { None }
    }
}

impl JournalImpl {
    pub closed spec fn wf(&self) -> bool {
        &&& self.fmt.valid()
        &&& match self.status {
            None => { self.index_builder is Some },
            Some(status) => { self.snapshot.boundary_lsn <= status.unmarshalled_tail_start }
        }
    }

    pub closed spec fn seq_start(&self) -> LSN {
        self.snapshot.boundary_lsn as nat
    }

    pub exec fn exec_seq_start(&self) -> (out: u64)
    ensures out == self.seq_start()
    {
        self.snapshot.boundary_lsn
    }

    pub closed spec fn freshest_rec(&self) -> Pointer
    {
        self.snapshot@.freshest_rec
    }

    pub exec fn exec_freshest_rec(&self) -> (out: Option<IAddress>)
    ensures 
        out is None ==> self.freshest_rec() is None,
        out is Some ==> self.freshest_rec() == Some(out.unwrap()@)
    {
        self.snapshot.freshest_rec
    }

//     pub closed spec fn last_marshalled_lsn(&self) -> LSN {
//         if self.snapshot.freshest_rec is Some {
//             // last item in that rec
//             7 as nat // well poop
//         } else {
//             self.snapshot.boundary_lsn as LSN
//         }
//     }
// 
//     pub exec fn exec_last_marshalled_lsn(&self) -> ILsn {
//         match self.snapshot.freshest_rec {
//             Some(ptr) => {
//                 // last item in that rec
//                 7 // well poop, I think we're going to want to maintain an index var and invariant
//             },
//             None => { self.snapshot.boundary_lsn },
//         }
//     }

    pub closed spec fn seq_end(&self) -> LSN {
        match &self.status {
            None => 0,
            Some(status) => {
                status.unmarshalled_tail_start as nat + status.unmarshalled_tail.len() as nat
            }
        }
    }

    pub exec fn exec_seq_end(&self) -> (out: ILsn)
    ensures out == self.seq_end()
    {
//         self.exec_last_marshalled_lsn() + self.status.unmarshalled_tail.len()
        match &self.status {
            None => 0,
            Some(status) => {
                // this cheat is incurring a runtime check, ugh
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

//     pub closed spec(checked) fn seq_end(&self) -> LSN
//     recommends self.index_ready()
//     {
//         self.status.unwrap().tail_as_history().seq_end
//     }

//     pub exec fn exec_seq_end(&self) -> (out: u64)
//     requires self.index_ready()
//     ensures out == self.seq_end()
//     {
//         match &self.status {
//             None => 0,
//             Some(status) => {
//                 // this cheat is incurring a runtime check, ugh
//                 if u64::MAX - status.unmarshalled_tail_start < status.unmarshalled_tail.len() as u64 {
//                     convert_overflow_into_liveness_failure();
//                 }
// 
//                 status.unmarshalled_tail_start + status.unmarshalled_tail.len() as u64
//             }
//         }
//     }

    // TODO(delete): dead code
//     pub exec fn new_empty(at_lsn: u64) -> (out: Self)
//     ensures
//         out.wf(),
//         !out.index_ready(),
//         out@.snapshot == IJournalSnapshot::spec_new_empty(at_lsn)@,
//     {
//         Self::new(IJournalSnapshot::new_empty(at_lsn))
//     }

    pub exec fn new(snapshot: IJournalSnapshot) -> (out: Self)
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
    pub exec fn recover_index_step(&mut self, cache: &mut FracCacheImpl) 
        -> (out: RecoverIndexResult) //(out: (bool, Option<(MutHandle, IAddress, Ghost<Cache::Label>)>, bool))
    requires
        old(self).wf(),
        !old(self).index_ready(),
        old(cache).wf(),
    ensures ({
        &&& self.wf()
        &&& self@.wf()
        &&& cache.wf()
        &&& match out {
            RecoverIndexResult::CacheLoad{slot_handle, addr} => {
                &&& self@ == old(self)@
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, slot_handle)
                &&& Cache::State::next(old(cache)@, cache@, cache_load_label(&addr))
            },
            RecoverIndexResult::IndexComplete{reads} => {
                let (cache_lbl, journal_lbl) = load_index_labels(reads@);
                &&& old(cache)@ == cache@
                &&& self.index_ready()
                &&& Cache::State::next(old(cache)@, cache@, cache_lbl)
                &&& CachedJournal::State::next(old(self)@, self@, journal_lbl)
            },
            RecoverIndexResult::IndexProgress{} => {
                &&& old(cache)@ == cache@
                &&& self@ == old(self)@
            }
        }
    })
    {
        let mut out = RecoverIndexResult::IndexProgress{};
        let mut index_builder = self.index_builder.take();
        index_builder = match index_builder {
            // NOTE: builder becomes None when we are out of the building phase
            None => { assert(false); None },
            // NOTE: builder is a hint for continued fetch
            Some(mut builder) => {
                match builder.next_head.freshest_rec {
                    None => { // this means all journal pages are fetched in cache, time to read indexes and build the pages
                        // NOTE: a silly implementation that forgets all computed updates if page is not available
                        let unmarshalled_tail = Vec::new();
                        let ghost mut reads = map!{};

                        reveal(Cache::State::next_by);
                        reveal(Cache::State::next);
                        reveal(CachedJournal::State::next_by);
                        reveal(CachedJournal::State::next);

                        // journal is not empty
                        if let Some(addr) = self.snapshot.freshest_rec {
                            let bdy = self.snapshot.boundary_lsn;
                            match cache.fetch(&addr) {
                                FetchErrorCode::Success{slot_handle} => {
                                    proof{ reads = reads.insert(addr@, slot_handle.rec@); }

                                    // unmarshall and parse the journal record
                                    let all_slice = Slice::all(&slot_handle.rec);
                                    assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                    assert( self.fmt.parsable(all_slice@.i(slot_handle.rec@)) ) by { assume( false ); }

                                    let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                    let i_seq_end = i_journal_record.seq_end();
                                    cache.handle_release(&addr, slot_handle);

                                    if bdy > i_seq_end { // invalid format
                                        please_panic();
                                    }
                                    assert(bdy <= i_seq_end);

                                    // let next_ptr = if 
                                    // while 


                                    // you want to 
                                    // let lsn_addr_index = build_lsn_addr_index_from_reads(reads, bdy, ptr, seq_end);

                                    
        // let seq_end = if ptr is Some { reads[ptr.unwrap()].message_seq.seq_end } else { bdy };
        // let lsn_addr_index = build_lsn_addr_index_from_reads(reads, bdy, ptr, seq_end);

                                // builder.next_head.freshest_rec = match i_journal_record.header.prior_rec 
                                //     {
                                //         None => None,
                                //         Some(iaddr) => { // cropped prior logic
                                //             if i_journal_record.header.start_lsn > self.snapshot.boundary_lsn {
                                //                 Some(iaddr)
                                //             } else { None }
                                //         }
                                //     };

                                    // slot_handle give us Irawpage
                                    // safe path
                                },
                                // TODO: handle more gracefully, fetch initiate should return 
                                // have a load_abort to give up the slot and remove the load
                                _ => {
                                    // we can also just set builder back to freshest rec, 
                                    // but panic here bc our current testing shouldn't reach that case
                                    please_panic(); 
                                } 
                            }
                            // fetch the page from cache

                        // let mut root = None;
                        // let mut next = self.snapshot.freshest_rec;
                        // let mut index = LsnAddrIndexImpl::new();

                        // while if let Some(addr) = next 

                        // i think you bdy just has to keep changing
                        //     invariant index@ == CachedJournal_v::build_lsn_addr_index_from_reads(reads, self.snapshot.boundary_lsn, root, )

                        // We got to the end of the journal linked list! We're done!
                        // self.status = Some(IJournalStatus::new(builder.next_head.boundary_lsn));
                        // assert( self.snapshot.boundary_lsn <= self.status.unwrap().unmarshalled_tail_start ) by {
                        //     assume( false ); // This needs to become an invariant of the builder process.
                        // }

                        // time to build the index?
                        // TODO: build index exec fn
                        // what has changed, nothing, in order to do this w
                        // what happens if we are ready
                        // we need to promise that journal index complete
                        // we need two promises 

        // let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        // let journal_lbl = CachedJournal::Label::LoadIndex{reads: to_journal_reads(reads)};
                            assume(false);
                        } else {
                            self.status = Some(IJournalStatus{
                                unmarshalled_tail,
                                lsn_addr_index: LsnAddrIndexImpl::new(),
                                unmarshalled_tail_start: self.snapshot.boundary_lsn
                            });

                            proof {
                                let (_, journal_lbl) = load_index_labels(reads);
                                let ptr = old(self)@.snapshot.freshest_rec;
                                let bdy = old(self)@.snapshot.boundary_lsn;
                                let journal_reads = to_journal_reads(reads);
                                let lsn_addr_index = CachedJournal_v::build_lsn_addr_index_from_reads(journal_reads, bdy, ptr, bdy);
                                assert(self@.status.unwrap().lsn_addr_index == lsn_addr_index);
                                assert(self@.status.unwrap().unmarshalled_tail == MsgHistory::empty_history_at(bdy));
                                assert( CachedJournal::State::load_index(old(self)@, self@, journal_lbl));
                                assert( CachedJournal::State::next_by(old(self)@, self@, journal_lbl, CachedJournal::Step::load_index{}) );
                                assert( CachedJournal::State::next(old(self)@, self@, journal_lbl) );    
                            }
                        }

                        proof {
                            let (cache_lbl, _) = load_index_labels(reads);
                            assert( old(cache)@ == cache@ );
                            assert( self.index_ready() );

                            let updated_entries = old(cache)@.write_updated_entries(cache_lbl->writes);
                            let updated_status_map = old(cache)@.write_updated_status(cache_lbl->writes);

                            assert(updated_entries =~= map!{});
                            assert(old(cache)@.entries.union_prefer_right(updated_entries) =~= old(cache)@.entries);
                            assert(updated_status_map =~= map!{});
                            assert(old(cache)@.status_map.union_prefer_right(updated_status_map) =~= old(cache)@.status_map);
                            assert( Cache::State::access(old(cache)@, cache@, cache_lbl));
                            assert( Cache::State::next_by(old(cache)@, cache@, cache_lbl, Cache::Step::access{}) );
                            assert( Cache::State::next(old(cache)@, cache@, cache_lbl) );               
                        }
                        out = RecoverIndexResult::IndexComplete{reads: Ghost(reads)};
                        None
                    },
                    Some(addr) => {
                        // Can we read the next page from the cache?
                        match cache.fetch(&addr) {
                            FetchErrorCode::LoadInitiate{slot_handle} => {
                                // release previous handle
                                // Cache is going to do a fetch and call us later. Bail out.
                                // Re-construct the struct
                                out = RecoverIndexResult::CacheLoad{slot_handle, addr};
                                Some(builder)
                            },
                            FetchErrorCode::Success{slot_handle} => {
                                let all_slice = Slice::all(&slot_handle.rec);
                                assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                assert( self.fmt.parsable(all_slice@.i(slot_handle.rec@)) ) by {
                                    assume( false ); // system invariant
                                }
                                let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                cache.handle_release(&addr, slot_handle);
                                builder.next_head.freshest_rec = match i_journal_record.header.prior_rec 
                                    {
                                        None => None,
                                        Some(iaddr) => { // cropped prior logic
                                            if i_journal_record.header.start_lsn > self.snapshot.boundary_lsn {
                                                Some(iaddr)
                                            } else { None }
                                        }
                                    };
                                Some(builder)
                            },
                            _ => {
                                Some(builder)
                            },
                        }
                    },
                }
            }
        };
        core::mem::swap(&mut self.index_builder, &mut index_builder);
        assert( self.wf() );
        out
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
        let mut dummy: Option<IJournalStatus> = None;
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

    // Provide a frozen snapshot for use in Implementation::send_superblock
    // Design intent:
    // - this exec call is really cheap, so it can be used both to "probe" what LSN we are able to
    // freeze to, as well as to capture that frozen sequence and use it in the superblock.
    // - This interface gives the journal design freedom to decide how to respond: A smarter
    // journal could keep track of what prior pages are clean and return just those. A lazy
    // journal (right now) just returns whatever it has lying around.
    // - The caller can use it in "probe" mode to decide that the LSN hasn't advanced enough,
    // and call some other interface to ask the journal to push the clean mark forward by cleaning
    // cache pages.

    pub exec fn freeze_journal(&self, cache: &FracCacheImpl) -> (out: FrozenJournal)
    requires
        self.index_ready(),
        self.marshalled_pages_are_clean(cache@),
    ensures
        out.wf(),
        out.snapshot.boundary_lsn == self.seq_start(),
        out.snapshot@ == self@.snapshot,
        out.seq_end as nat == self@.marshalled_seq_end(),
        self.lsns_are_clean(cache@, out),
    {
        assume(false);  // TODO: prove lsns_are_clean from precondition
        FrozenJournal{
            snapshot: self.snapshot.clone(),
            seq_end: self.status.as_ref().unwrap().unmarshalled_tail_start,
        }
    }

    pub open spec fn lsn_range(start_incl: LSN, end_excl: LSN) -> Set<LSN>
    {
        Set::new(|lsn: LSN| start_incl <= lsn && lsn < end_excl)
    }

    // Open because this definition gets used proving the refinement CachedJournal::Step::freeze_for_commit(depth) in Implementation
    pub open spec fn iaddrs_for_lsns(self, start_incl: LSN, end_excl: LSN) -> Set<Address>
    recommends self.index_ready()
    {
        self@.status.unwrap().lsn_addr_index.restrict(Self::lsn_range(start_incl, end_excl)).values()
    }

    /// All marshalled journal pages are Filled+Clean in cache.
    pub open spec fn marshalled_pages_are_clean(&self, cache: Cache::State) -> bool
    recommends self.index_ready()
    {
        Cache::State::next_by(cache, cache,
            Cache::Label::EvictableCheck{addrs: self.iaddrs_for_lsns(self.seq_start() as LSN, self@.marshalled_seq_end())},
            Cache::Step::evictable())
    }

    pub open spec fn lsns_are_clean(&self, cache: Cache::State, out: FrozenJournal) -> bool
    {
        Cache::State::next_by(cache, cache,
            Cache::Label::EvictableCheck{addrs: self.iaddrs_for_lsns(out.seq_start() as LSN, out.seq_end as LSN)},
            Cache::Step::evictable())
    }

//     // TODO maybe fold this promise right into a smarter freeze_journal, and then add a method that
//     // advances the clean watermark and provides a callback to let the caller know it could maybe
//     // sync more stuff now.
//     pub exec fn check_lsns_are_clean(&self, cache: &FracCacheImpl, out: FrozenJournal) -> (clean: bool)
//     ensures clean ==> self.lsns_are_clean(cache@, out)
//     {
//         proof { assume(false); }
//         true
//     }

    /// Check whether the journal is marshalled and clean up to target_lsn.
    /// Returns true iff:
    ///   - target_lsn <= marshalled_seq_end (marshalled far enough)
    ///   - all journal page addrs in [seq_start, marshalled_seq_end) are Filled+Clean in cache
    /// If not ready, may do work (marshal tail, poke cache to flush) and return false;
    /// caller should retry later.
    pub exec fn clean_for_commit(&self, cache: &FracCacheImpl, target_lsn: ILsn) -> (ready: bool)
    requires
        self.index_ready(),
    ensures
        ready ==> target_lsn <= self@.marshalled_seq_end(),
        ready ==> self.marshalled_pages_are_clean(cache@),
    {
        assume(false);  // TODO: real implementation
        false
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
