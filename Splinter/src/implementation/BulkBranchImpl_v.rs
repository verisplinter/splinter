// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::arithmetic::mul::lemma_mul_basics;

use crate::implementation::CachedBranch_v::{CachedBranch, LoadedBranch};
use crate::implementation::CachedBranch_v::loaded_initialize_write_nodes;
use crate::implementation::MemtableImpl_v::{MemtableBucket, MemtableEntry};
use crate::implementation::MemtableImpl_v::MemtableImpl;
use crate::implementation::BranchBulkBuilderImpl_v::{
    BranchBulkBuilder, BranchBulkNodeResult, BranchBulkStartResult,
};
use crate::implementation::StreamingBranchBuilderImpl_v::{
    StreamingBranchBuilder, StreamingBranchPhase,
    StreamingBuilderInputResult, StreamingFinishInputResult,
    StreamingFinishLevelResult, StreamingPendingPage,
};
use crate::implementation::CachedBulkBranch_v::{
    CachedBulkBranch, CachedBulkBranchEvent, CachedBulkBranchPhase,
};
use crate::implementation::AuPoolImpl_v::iau_vec_set;
use crate::implementation::BranchPageImpl_v::{
    auxiliary_branch_node_marshallable, index_branch_node_marshallable,
    branch_index_capacity, branch_index_capacity_spec,
    branch_leaf_capacity, branch_leaf_capacity_spec,
    leaf_branch_node_marshallable, marshall_branch_node_page,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachingDiskBranchBetree_v::to_branch_nodes;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::CachedBranchBetree_v::{
    loaded_sealed_branch, valid_loaded_sealed_branch,
};
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, PrepareTwoWriteResult,
    ReserveWriteResult,
};
use crate::implementation::IBranchNode_v::{IBranchNode, iau_seq, iopt_addr};
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::spec::ImplDisk_t::{IAddress, IAU};
use crate::spec::ImplDisk_t::IPage;
use crate::disk::GenericDisk_v::{Address, addrs_closed, page_count};
use crate::spec::AsyncDisk_t::RawPage;
use crate::marshalling::IBranchNodeFormat_v::BranchNodePageFmt;
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::betree::PivotBranch_v::Node as PivotNode;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};

verus! {

pub enum BulkBuilderImpl {
    Memtable { memtable: BranchBulkBuilder },
    Streaming { streaming: StreamingBranchBuilder },
}

pub struct BulkBranchImpl {
    pub root: Option<IAddress>,
    pub root_node: Option<IBranchNode>,
    pub mini_allocator: MiniAllocatorImpl,
    pub sealed: bool,
    pub bulk_builder: Option<BulkBuilderImpl>,
    pub sealed_branch: Ghost<Option<LinkedBranch<Summary>>>,
    pub sealed_source: Ghost<Option<Map<Key, Message>>>,
}

pub struct WipLeafContents {
    pub keys: Vec<Key>,
    pub msgs: Vec<Message>,
}

pub enum BulkBranchInitializeResult {
    Initialized {
        root: IAddress,
        prepared_cache: Ghost<Cache::State>,
        writes: Ghost<Map<Address, RawPage>>,
        event: Ghost<CachedBulkBranchEvent>,
    },
    NeedsAUs,
    CacheFull,
    Blocked,
}

pub enum BulkBranchSealResult {
    Sealed {
        reads: Ghost<Map<Address, RawPage>>,
        event: Ghost<CachedBulkBranchEvent>,
    },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BulkBranchReadResult {
    Read { reads: Ghost<Map<Address, RawPage>> },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BulkStartResult {
    Started,
    Empty,
    Overflow,
    InvalidCapacity,
    Blocked,
}

pub enum StreamingBulkFinishResult {
    Empty,
    Continue,
    PagesReady,
    RootReady,
    Blocked,
}

pub enum BulkStageResult {
    Staged {
        addr: IAddress,
        prepared_cache: Ghost<Cache::State>,
        writes: Ghost<Map<Address, RawPage>>,
        event: Ghost<CachedBulkBranchEvent>,
    },
    NeedsAUs,
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BulkSealResult {
    Sealed {
        root: IAddress,
        aux_ptr: Option<IAddress>,
        prepared_cache: Ghost<Cache::State>,
        writes: Ghost<Map<Address, RawPage>>,
        event: Ghost<CachedBulkBranchEvent>,
        deallocs: Vec<IAU>,
        branch: Ghost<LinkedBranch<Summary>>,
    },
    NeedsAUs,
    CacheFull,
    Blocked,
    InvalidPage,
}

impl WipLeafContents {
    pub fn from_sorted_entries(
        entries: &Vec<MemtableEntry>,
    ) -> (out: Self)
        requires
            MemtableBucket::strictly_sorted(entries@),
        ensures
            out.keys@ == entries@.map(
                |i: int, entry: MemtableEntry| entry.key,
            ),
            out.msgs@ == entries@.map(
                |i: int, entry: MemtableEntry| entry.message,
            ),
            out.keys.len() == out.msgs.len(),
            Key::is_strictly_sorted(out.keys@),
    {
        let mut keys = Vec::new();
        let mut msgs = Vec::new();
        let mut idx = 0usize;
        while idx < entries.len()
            invariant
                idx <= entries.len(),
                keys@ == entries@.subrange(0, idx as int).map(
                    |i: int, entry: MemtableEntry| entry.key,
                ),
                msgs@ == entries@.subrange(0, idx as int).map(
                    |i: int, entry: MemtableEntry| entry.message,
                ),
            decreases entries.len() - idx,
        {
            keys.push(entries[idx].key);
            msgs.push(entries[idx].message);
            idx += 1;
        }
        proof {
            assert(entries@.subrange(0, entries@.len() as int) == entries@);
            assert forall |i: int, j: int|
                0 <= i < j < keys@.len()
                implies Key::lt(keys@[i], keys@[j]) by {
                assert(keys@[i] == entries@[i].key);
                assert(keys@[j] == entries@[j].key);


            }
        }
        Self { keys, msgs }
    }
}

impl BulkBranchImpl {
    pub open spec fn staged_nodes(&self) -> LoadedBranch {
        match self.bulk_builder {
            Some(BulkBuilderImpl::Memtable { ref memtable }) => {
                memtable.staged_nodes@
            },
            Some(BulkBuilderImpl::Streaming { ref streaming }) => {
                streaming.staged_nodes@
            },
            None => Map::empty(),
        }
    }

    pub open spec fn has_memtable_builder(&self) -> bool {
        self.bulk_builder is Some
            && self.bulk_builder->0 is Memtable
    }

    pub open spec fn memtable_builder(&self) -> BranchBulkBuilder
        recommends self.has_memtable_builder(),
    {
        self.bulk_builder->0->memtable
    }

    pub open spec fn has_streaming_builder(&self) -> bool {
        self.bulk_builder is Some
            && self.bulk_builder->0 is Streaming
    }

    pub open spec fn streaming_builder(&self) -> StreamingBranchBuilder
        recommends self.has_streaming_builder(),
    {
        self.bulk_builder->0->streaming
    }

    pub open spec fn allocated_pages(&self) -> Set<Address> {
        Set::new(|addr: Address| {
            &&& self.mini_allocator.i().allocs.contains_key(addr.au)
            &&& self.mini_allocator.i().allocs[addr.au]
                .allocated.contains(addr)
        })
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.mini_allocator.wf()
        &&& MiniAllocatorImpl::allocators_unique(
            self.mini_allocator.allocators@,
        )
        &&& match self.root {
            Some(root) => {
                &&& root@.wf()
                &&& self.mini_allocator.i().all_aus().contains(root@.au)
                &&& self.root_node is Some
                &&& self.root_node->0.wf()
                &&& !(self.root_node->0 is Auxiliary)
                &&& self.root_node->0@.wf()
                &&& self.root_node->0@.keys_strictly_sorted()
            },
            None => self.root_node is None && !self.sealed,
        }
        &&& match self.bulk_builder {
            Some(BulkBuilderImpl::Memtable { ref memtable }) => {
                &&& self.root is None
                &&& self.root_node is None
                &&& !self.sealed
                &&& BranchBulkBuilder::staged_nodes_wf(
                    memtable.staged_nodes@,
                )
                &&& memtable.staged_nodes@.dom()
                    == self.allocated_pages()
                &&& self.sealed_branch@ is None
                &&& self.sealed_source@ is None
            },
            Some(BulkBuilderImpl::Streaming { ref streaming }) => {
                &&& self.root is None
                &&& self.root_node is None
                &&& !self.sealed
                &&& streaming.local_wf()
                &&& streaming.leaf_tail.capacity as int
                    == branch_leaf_capacity_spec()
                &&& streaming.index_fanout as int
                    == branch_index_capacity_spec() + 1
                &&& BranchBulkBuilder::staged_nodes_wf(
                    streaming.staged_nodes@,
                )
                &&& streaming.staged_nodes@.dom()
                    == self.allocated_pages()
                &&& self.sealed_branch@ is None
                &&& self.sealed_source@ is None
            },
            None => true,
        }
        &&& match self.sealed_branch@ {
            Some(branch) => {
                &&& self.sealed
                &&& self.root is Some
                &&& self.sealed_source@ is Some
                &&& branch.root == self.root.unwrap()@
                &&& branch.valid_sealed_branch()
                &&& branch.tight_disk_view_with_summary()
                &&& branch.get_summary()
                    == self.mini_allocator.i().all_aus()
                &&& branch.i().i().map == self.sealed_source@.unwrap()
            },
            None => self.sealed_source@ is None,
        }
    }

    pub open spec fn i(&self) -> CachedBulkBranch {
        CachedBulkBranch {
            phase: if self.sealed {
                CachedBulkBranchPhase::Sealed {
                    branch: self.sealed_branch@.unwrap(),
                }
            } else {
                CachedBulkBranchPhase::Building {
                    staged_nodes: self.staged_nodes(),
                }
            },
            mini_allocator: self.mini_allocator.i(),
        }
    }

    pub open spec fn cache_inv(&self, cache: Cache::State) -> bool {
        &&& (self.root is Some ==> {
            let root = self.root.unwrap()@;
            &&& self.root_node is Some
            &&& exists |raw: RawPage|
                cache.valid_read(root, raw)
                && BranchNodePageFmt::spec_new().parsable(raw)
                && raw_page_to_branch_node(raw) == self.root_node->0@
        })
        &&& forall |addr: Address|
            #[trigger] self.staged_nodes().contains_key(addr) ==> {
                exists |raw: RawPage|
                    cache.valid_read(addr, raw)
                    && BranchNodePageFmt::spec_new().parsable(raw)
                    && raw_page_to_branch_node(raw)
                        == self.staged_nodes()[addr]
            }
        &&& match self.sealed_branch@ {
            Some(branch) => forall |addr: Address|
                #[trigger] branch.disk_view.entries.contains_key(addr)
                ==> exists |raw: RawPage|
                    cache.valid_read(addr, raw)
                    && BranchNodePageFmt::spec_new().parsable(raw)
                    && raw_page_to_branch_node(raw)
                        == branch.disk_view.entries[addr],
            None => true,
        }
    }

    pub proof fn cache_inv_preserved_by_valid_reads(
        &self,
        old_cache: Cache::State,
        new_cache: Cache::State,
    )
        requires
            self.cache_inv(old_cache),
            forall |addr: Address, data: RawPage|
                old_cache.valid_read(addr, data)
                ==> new_cache.valid_read(addr, data),
        ensures
            self.cache_inv(new_cache),
    {

    }

    pub open spec fn sealed_branch_raw(
        cache: Cache::State,
        branch: LinkedBranch<Summary>,
        addr: Address,
    ) -> RawPage {
        choose |raw: RawPage|
            cache.valid_read(addr, raw)
            && BranchNodePageFmt::spec_new().parsable(raw)
            && raw_page_to_branch_node(raw)
                == branch.disk_view.entries[addr]
    }

    pub open spec fn represents_buffer(&self, buffer: SimpleBuffer) -> bool {
        self.root_node is Some
        && self.root_node->0@ is Leaf
        && (PivotNode::Leaf {
            keys: self.root_node->0@->keys,
            msgs: self.root_node->0@->msgs,
        }).i() == buffer
    }

    pub open spec fn bulk_builder_wf(
        &self,
        memtable: &MemtableImpl,
    ) -> bool {
        match self.bulk_builder {
            Some(BulkBuilderImpl::Memtable { memtable: ref builder }) => {
                builder.wf(memtable)
            },
            Some(BulkBuilderImpl::Streaming { ref streaming }) => {
                streaming.local_wf()
            },
            None => true,
        }
    }

    pub open spec fn builder_page_ready(&self) -> bool {
        ||| self.has_memtable_builder()
            && (self.memtable_builder().phase is Leaves
                || self.memtable_builder().phase is Index)
        ||| self.has_streaming_builder()
            && self.streaming_builder().pending is Some
            && (self.streaming_builder().phase is Reading
                || self.streaming_builder().phase is Finishing)
    }

    pub open spec fn builder_ready_to_seal(&self) -> bool {
        ||| self.has_memtable_builder()
            && (self.memtable_builder().phase is ReadyLeafRoot
                || self.memtable_builder().phase is ReadyIndexRoot)
        ||| self.has_streaming_builder()
            && (self.streaming_builder().phase is ReadyLeafRoot
                || self.streaming_builder().phase is ReadyIndexRoot)
    }

    pub open spec fn builder_source_map(&self) -> Map<Key, Message>
        recommends self.bulk_builder is Some,
    {
        match self.bulk_builder->0 {
            BulkBuilderImpl::Memtable { ref memtable } => memtable.source@,
            BulkBuilderImpl::Streaming { ref streaming } => {
                MemtableBucket::entries_map(streaming.source_entries@)
            },
        }
    }

    pub fn new(free_au_threshold: IAU) -> (out: Self)
        ensures
            out.wf(),
            out@ == CachedBulkBranch::new(Set::empty()),
            out.bulk_builder is None,
            out.mini_allocator.i() == MiniAllocator::empty(),
            forall |total_aus: IAU| out.mini_allocator.bounded(total_aus),
    {
        let mini_allocator = MiniAllocatorImpl::empty(free_au_threshold);
        let out = Self {
            root: None,
            root_node: None,
            mini_allocator,
            sealed: false,
            bulk_builder: None,
            sealed_branch: Ghost(None),
            sealed_source: Ghost(None),
        };
        proof {
            let empty = crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty();
            assert(out.mini_allocator.i() == empty);
            assert(empty.add_aus(Set::<crate::disk::GenericDisk_v::AU>::empty())
                == empty) by {

                assert(empty.add_aus(Set::empty()).allocs
                    =~= Map::empty());
            }

            assert(out.wf());
        }
        out
    }

    pub fn fill_aus(&mut self, aus: Vec<IAU>)
        requires
            old(self).wf(),
            !old(self).sealed,
            MiniAllocatorImpl::iau_seq_unique(aus@),
            iau_vec_set(aus@).disjoint(
                MiniAllocatorImpl::allocators_au_set(
                    old(self).mini_allocator.allocators@,
                ),
            ),
        ensures
            self.wf(),
            self.bulk_builder == old(self).bulk_builder,
            self.mini_allocator.i()
                == old(self).mini_allocator.i().add_aus(iau_vec_set(aus@)),
            forall |total_aus: IAU|
                old(self).mini_allocator.bounded(total_aus)
                && (forall |i: int| 0 <= i < aus@.len() ==> {
                    &&& 0 < (#[trigger] aus@[i] as nat)
                    &&& (aus@[i] as nat) < total_aus as nat
                })
                ==> self.mini_allocator.bounded(total_aus),
            CachedBulkBranch::fill_next(
                old(self)@,
                self@,
                iau_vec_set(aus@),
                Set::empty(),
            ),
    {
        self.mini_allocator.add_aus(aus);
        proof {
            assert(self.allocated_pages()
                == old(self).allocated_pages()) by {
                assert_sets_equal!(
                    self.allocated_pages(),
                    old(self).allocated_pages(),
                    addr => {
                        if self.allocated_pages().contains(addr)
                            && !old(self).allocated_pages().contains(addr)
                        {
                            assert(iau_vec_set(aus@).contains(addr.au));
                            assert(self.mini_allocator.i().allocs[addr.au]
                                == crate::allocation_layer::MiniAllocator_v::PageAllocator::new(
                                    addr.au,
                                ));
                            assert(!self.mini_allocator.i().allocs[addr.au]
                                .allocated.contains(addr));
                        }
                    }
                );
            }



            assert(self.wf());
        }
    }

    pub fn begin_bulk_build(
        &mut self,
        memtable: &MemtableImpl,
    ) -> (result: BulkStartResult)
        requires
            old(self).wf(),
            old(self).bulk_builder is None,
            old(self).root is None,
            old(self).allocated_pages().is_empty(),
            memtable.wf(),
        ensures
            self.wf(),
            self@ == old(self)@,
            match result {
                BulkStartResult::Started => {
                    &&& self.has_memtable_builder()
                    &&& self.memtable_builder().wf(memtable)
                    &&& self.memtable_builder().source@
                        == memtable@.buffer.map
                },
                BulkStartResult::Empty
                | BulkStartResult::Overflow
                | BulkStartResult::InvalidCapacity
                | BulkStartResult::Blocked => {
                    *self == *old(self)
                },
            },
    {
        match BranchBulkBuilder::start(memtable) {
            BranchBulkStartResult::Started { builder } => {
                self.bulk_builder = Some(BulkBuilderImpl::Memtable {
                    memtable: builder,
                });
                proof {
                    assert(self.staged_nodes()
                        == LoadedBranch::empty());
                    assert(self.wf());
                    assert(self@ == old(self)@);
                }
                BulkStartResult::Started
            },
            BranchBulkStartResult::Empty => BulkStartResult::Empty,
            BranchBulkStartResult::Overflow => {
                BulkStartResult::Overflow
            },
            BranchBulkStartResult::InvalidCapacity => {
                BulkStartResult::InvalidCapacity
            },
        }
    }

    pub fn begin_streaming_build(
        &mut self,
    ) -> (result: BulkStartResult)
        requires
            old(self).wf(),
            old(self).bulk_builder is None,
            old(self).root is None,
            old(self).allocated_pages().is_empty(),
        ensures
            self.wf(),
            self@ == old(self)@,
            self.mini_allocator == old(self).mini_allocator,
            match result {
                BulkStartResult::Started => {
                    &&& self.has_streaming_builder()
                    &&& self.streaming_builder().local_wf()
                    &&& self.streaming_builder().phase is Reading
                    &&& self.streaming_builder().source_entries@.len() == 0
                },
                BulkStartResult::Empty
                | BulkStartResult::Overflow
                | BulkStartResult::InvalidCapacity
                | BulkStartResult::Blocked => *self == *old(self),
            },
    {
        let leaf_capacity = branch_leaf_capacity();
        let index_capacity = branch_index_capacity();
        if index_capacity == usize::MAX {
            return BulkStartResult::InvalidCapacity;
        }
        let builder = match StreamingBranchBuilder::new(
            leaf_capacity,
            index_capacity + 1,
        ) {
            Some(builder) => builder,
            None => return BulkStartResult::InvalidCapacity,
        };
        self.bulk_builder = Some(BulkBuilderImpl::Streaming {
            streaming: builder,
        });
        proof {
            assert(self.staged_nodes() == LoadedBranch::empty());
            assert(BranchBulkBuilder::staged_nodes_wf(
                self.staged_nodes(),
            ));
            assert(self.wf());
            assert(self@ == old(self)@);
        }
        BulkStartResult::Started
    }

    pub fn push_streaming_entry(
        &mut self,
        entry: MemtableEntry,
    ) -> (out: StreamingBuilderInputResult)
        requires
            old(self).wf(),
            old(self).has_streaming_builder(),
            old(self).streaming_builder().phase is Reading,
            old(self).streaming_builder().pending is None,
            old(self).streaming_builder().deferred is None,
            forall |i: int|
                0 <= i < old(self).streaming_builder().source_entries@.len()
                ==> (#[trigger]
                    old(self).streaming_builder().source_entries@[i]).key.0
                        < entry.key.0,
        ensures
            self.wf(),
            self@ == old(self)@,
            self.mini_allocator == old(self).mini_allocator,
            self.has_streaming_builder(),
            self.streaming_builder().local_wf(),
            self.streaming_builder().phase is Reading,
            self.streaming_builder().source_entries@
                == old(self).streaming_builder().source_entries@.push(entry),
            self.streaming_builder().staged_nodes@
                == old(self).streaming_builder().staged_nodes@,
            match out {
                StreamingBuilderInputResult::Accepted => {
                    self.streaming_builder().pending is None
                },
                StreamingBuilderInputResult::PageReady => {
                    self.streaming_builder().pending is Some
                },
            },
    {
        let builder_opt = self.bulk_builder.take();
        let mut builder = match builder_opt.unwrap() {
            BulkBuilderImpl::Streaming { streaming } => streaming,
            _ => {
                proof { assert(false); }
                unreached()
            },
        };
        let out = builder.push_entry(entry);
        self.bulk_builder = Some(BulkBuilderImpl::Streaming {
            streaming: builder,
        });
        proof {
            assert(self.allocated_pages()
                == old(self).allocated_pages());
            assert(self.wf());
            assert(self@ == old(self)@);
        }
        out
    }

    pub fn finish_streaming_input(
        &mut self,
    ) -> (out: StreamingFinishInputResult)
        requires
            old(self).wf(),
            old(self).has_streaming_builder(),
            old(self).streaming_builder().phase is Reading,
            old(self).streaming_builder().pending is None,
            old(self).streaming_builder().deferred is None,
        ensures
            self.wf(),
            self@ == old(self)@,
            self.mini_allocator == old(self).mini_allocator,
            forall |cache: Cache::State|
                self.cache_inv(cache) == old(self).cache_inv(cache),
            self.has_streaming_builder(),
            self.streaming_builder().local_wf(),
            self.streaming_builder().source_entries@
                == old(self).streaming_builder().source_entries@,
            self.streaming_builder().staged_nodes@
                == old(self).streaming_builder().staged_nodes@,
            match out {
                StreamingFinishInputResult::Empty => {
                    self.streaming_builder().phase is Empty
                },
                StreamingFinishInputResult::RootReady => {
                    self.streaming_builder().phase is ReadyLeafRoot
                },
                StreamingFinishInputResult::Continue => {
                    self.streaming_builder().phase is Finishing
                },
            },
    {
        let builder_opt = self.bulk_builder.take();
        let mut builder = match builder_opt.unwrap() {
            BulkBuilderImpl::Streaming { streaming } => streaming,
            _ => {
                proof { assert(false); }
                unreached()
            },
        };
        let out = builder.finish_input();
        self.bulk_builder = Some(BulkBuilderImpl::Streaming {
            streaming: builder,
        });
        proof {
            assert(self.allocated_pages()
                == old(self).allocated_pages());
            assert(self.wf());
            assert(self@ == old(self)@);
        }
        out
    }

    pub fn finish_streaming_level(
        &mut self,
    ) -> (out: StreamingFinishLevelResult)
        requires
            old(self).wf(),
            old(self).has_streaming_builder(),
            old(self).streaming_builder().phase is Finishing,
            old(self).streaming_builder().pending is None,
            old(self).streaming_builder().deferred is None,
        ensures
            self.wf(),
            self@ == old(self)@,
            self.mini_allocator == old(self).mini_allocator,
            forall |cache: Cache::State|
                self.cache_inv(cache) == old(self).cache_inv(cache),
            self.has_streaming_builder(),
            self.streaming_builder().local_wf(),
            self.streaming_builder().source_entries@
                == old(self).streaming_builder().source_entries@,
            self.streaming_builder().staged_nodes@
                == old(self).streaming_builder().staged_nodes@,
            match out {
                StreamingFinishLevelResult::Empty => {
                    self.streaming_builder().phase is Empty
                },
                StreamingFinishLevelResult::Advanced
                | StreamingFinishLevelResult::PagesReady => {
                    self.streaming_builder().phase is Finishing
                },
                StreamingFinishLevelResult::RootReady => {
                    self.streaming_builder().phase is ReadyIndexRoot
                },
            },
    {
        let builder_opt = self.bulk_builder.take();
        let mut builder = match builder_opt.unwrap() {
            BulkBuilderImpl::Streaming { streaming } => streaming,
            _ => {
                proof { assert(false); }
                unreached()
            },
        };
        let out = builder.finish_level();
        self.bulk_builder = Some(BulkBuilderImpl::Streaming {
            streaming: builder,
        });
        proof {
            assert(self.allocated_pages()
                == old(self).allocated_pages());
            assert(self.wf());
            assert(self@ == old(self)@);
        }
        out
    }

    pub fn stage_bulk_page_with_cache(
        &mut self,
        memtable: &MemtableImpl,
        cache: &mut FracCacheImpl,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (result: BulkStageResult)
        requires
            old(self).wf(),
            old(self).bulk_builder is Some,
            old(self).bulk_builder_wf(memtable),
            old(self).builder_page_ready(),
            old(self).mini_allocator.bounded(disk_au_count),
            old(cache).wf(),
            old(cache)@.inv(),
            old(self).cache_inv(old(cache)@),
            0 < disk_page_count as nat,
            disk_page_count as nat == page_count(),
        ensures
            self.wf(),
            self.bulk_builder_wf(memtable),
            old(self).has_streaming_builder() ==> {
                &&& self.has_streaming_builder()
                &&& self.streaming_builder().phase
                    == old(self).streaming_builder().phase
                &&& self.streaming_builder().source_entries@
                    == old(self).streaming_builder().source_entries@
            },
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BulkStageResult::Staged {
                    addr,
                    prepared_cache,
                    writes,
                    event,
                } => {
                    &&& self.bulk_builder is Some
                    &&& (self.has_memtable_builder()
                        <==> old(self).has_memtable_builder())
                    &&& (self.has_streaming_builder()
                        <==> old(self).has_streaming_builder())
                    &&& self.mini_allocator.i().all_aus()
                        == old(self).mini_allocator.i().all_aus()
                    &&& self.mini_allocator.bounded(disk_au_count)
                    &&& event@ == CachedBulkBranchEvent::StagePage {
                        addr: addr@,
                        write_nodes: to_branch_nodes(writes@),
                    }
                    &&& writes@.dom() == set![addr@]
                    &&& writes@.dom() <= addresses_in_aus(
                        old(self).mini_allocator.i().all_aus(),
                    )
                    &&& self.cache_inv(cache@)
                    &&& CachedBulkBranch::build_next(
                        old(self)@,
                        self@,
                        event@,
                        Set::empty(),
                        Set::empty(),
                    )
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: Map::empty(),
                            writes: writes@,
                        },
                    )
                },
                BulkStageResult::NeedsAUs
                | BulkStageResult::CacheFull
                | BulkStageResult::Blocked
                | BulkStageResult::InvalidPage => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                },
            },
    {
        if !self.mini_allocator.is_allocation_ready() {
            return BulkStageResult::NeedsAUs;
        }
        let addr = self.mini_allocator.peek_next_addr();
        if addr.page >= disk_page_count {
            return BulkStageResult::NeedsAUs;
        }
        proof {
            self.mini_allocator.prove_active_next_addr_can_allocate(
                disk_au_count,
                disk_page_count,
            );
            assert(addr@.wf());
            assert(!self.staged_nodes().contains_key(addr@)) by {
                if self.staged_nodes().contains_key(addr@) {
                    assert(self.allocated_pages().contains(addr@));
                    assert(self.mini_allocator.i().allocs[addr@.au]
                        .allocated.contains(addr@));
                    assert(!self.mini_allocator.i().can_allocate(addr@));
                }
            }
        }

        let ghost cache0 = *cache;
        let mut reserved = false;
        let mut handle = if cache.contains_addr(&addr) {
            match cache.fetch(&addr, false) {
                FetchErrorCode::Success { slot_handle } => slot_handle,
                FetchErrorCode::CacheFull => {
                    return BulkStageResult::CacheFull;
                },
                FetchErrorCode::Awaiting
                | FetchErrorCode::NotPresent => {
                    return BulkStageResult::Blocked;
                },
                FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                    proof { assert(false); }
                    return BulkStageResult::Blocked;
                },
            }
        } else {
            reserved = true;
            match cache.reserve_for_write_absent(&addr) {
                ReserveWriteResult::Reserved { slot_handle } => slot_handle,
                ReserveWriteResult::CacheFull => {
                    return BulkStageResult::CacheFull;
                },
            }
        };
        let ghost borrowed_cache = *cache;
        let ghost prepared_cache = if reserved {
            borrowed_cache@
        } else {
            cache0@
        };
        proof {
            if !reserved {
                FracCacheImpl::valid_write_handle_model_entry(
                    &borrowed_cache,
                    &addr,
                    handle,
                );
            }
        }

        let builder_opt = self.bulk_builder.take();
        let (node, descriptor, post_builder) = match builder_opt.unwrap() {
            BulkBuilderImpl::Memtable { memtable: mut builder } => {
                let node_result = builder.stage_next(memtable, addr);
                let (node, descriptor) = match node_result {
                    BranchBulkNodeResult::Page { node, descriptor } => {
                        (node, descriptor)
                    },
                    BranchBulkNodeResult::NotReady => {
                        proof { assert(false); }
                        self.bulk_builder = Some(BulkBuilderImpl::Memtable {
                            memtable: builder,
                        });
                        return BulkStageResult::Blocked;
                    },
                };
                (node, descriptor, BulkBuilderImpl::Memtable {
                    memtable: builder,
                })
            },
            BulkBuilderImpl::Streaming { mut streaming } => {
                let staged = match streaming.pending.as_ref().unwrap() {
                    StreamingPendingPage::Leaf { .. } => {
                        proof {
                            streaming.pending_leaf_has_leaf_deferred();
                        }
                        streaming.stage_pending_leaf(addr)
                    },
                    StreamingPendingPage::Index { .. } => {
                        streaming.stage_pending_index(addr)
                    },
                };
                (staged.node, staged.descriptor,
                    BulkBuilderImpl::Streaming { streaming })
            },
        };
        self.bulk_builder = Some(post_builder);
        proof {
            let fmt = BranchNodePageFmt::spec_new();
            if node is Leaf {
                if old(self).has_streaming_builder() {
                    assert(node->keys.len() as int
                        <= branch_leaf_capacity_spec());
                }
                leaf_branch_node_marshallable(&node);
            } else {
                assert(node is Index);
                if old(self).has_streaming_builder() {
                    assert(node->pivots.len() as int
                        <= branch_index_capacity_spec());
                }
                index_branch_node_marshallable(&node);
            }
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(node));
            assert(fmt.spec_size(node.parsedv())
                == crate::implementation::FracCacheImpl_v::PAGE_SIZE_BYTES);
        }
        let ghost node_view = node@;
        let page = marshall_branch_node_page(&node);
        let ghost page_view = page@;
        let ghost writes = map![addr@ => page_view];
        let allocated = self.mini_allocator.allocate_fresh_addr_checked(
            disk_au_count,
            disk_page_count,
        );
        proof {
            assert(allocated is Some);
            assert(allocated.unwrap() == addr);
        }
        handle.rec = page;
        let slot = handle.idx;
        proof {
            assert(cache.valid_write_handle(&addr, handle));
            assert(cache@.valid_write(addr@));
        }
        cache.write_release(&addr, handle);
        let ghost event = CachedBulkBranchEvent::StagePage {
            addr: addr@,
            write_nodes: to_branch_nodes(writes),
        };
        proof {
            if reserved {
                assert(Cache::State::next(
                    cache0@,
                    prepared_cache,
                    Cache::Label::Internal,
                ));
                assert(Cache::State::next(
                    prepared_cache,
                    cache@,
                    Cache::Label::Access {
                        reads: Map::empty(),
                        writes,
                    },
                ));
            } else {
                reveal(Cache::State::next);
                reveal(Cache::State::next_by);
                assert(Cache::State::next_by(
                    cache0@,
                    cache0@,
                    Cache::Label::Internal,
                    Cache::Step::noop(),
                ));
                assert(Cache::State::next(
                    cache0@,
                    prepared_cache,
                    Cache::Label::Internal,
                ));
                Cache::State::access_from_borrowed_write_slot(
                    cache0@,
                    borrowed_cache@,
                    cache@,
                    Map::empty(),
                    addr@,
                    slot,
                    page_view,
                );
            }
            assert(to_branch_nodes(writes)[addr@] == node_view);
            assert(to_branch_nodes(writes).dom() == set![addr@]) by {
                assert_sets_equal!(
                    to_branch_nodes(writes).dom(),
                    set![addr@],
                    candidate => {}
                );
            }
            assert(self.staged_nodes()
                == old(self).staged_nodes().insert(addr@, node_view));
            assert(self.allocated_pages()
                == old(self).allocated_pages().insert(addr@)) by {
                assert_sets_equal!(
                    self.allocated_pages(),
                    old(self).allocated_pages().insert(addr@),
                    candidate => {}
                );
            }
            assert(prepared_cache.inv()) by {
                if reserved {
                    Cache::State::inv_next(
                        cache0@,
                        prepared_cache,
                        Cache::Label::Internal,
                    );
                }
            }
            assert(cache@.valid_read(addr@, page_view));
            assert forall |candidate: Address|
                #[trigger] self.staged_nodes().contains_key(candidate)
                implies {
                    exists |raw: RawPage|
                        cache@.valid_read(candidate, raw)
                        && BranchNodePageFmt::spec_new().parsable(raw)
                        && raw_page_to_branch_node(raw)
                            == self.staged_nodes()[candidate]
                } by {
                if candidate == addr@ {
                    assert(BranchNodePageFmt::spec_new()
                        .parsable(page_view));
                    assert(raw_page_to_branch_node(page_view)
                        == node_view);
                } else {
                    assert(old(self).staged_nodes()
                        .contains_key(candidate));
                    let raw = choose |raw: RawPage|
                        cache0@.valid_read(candidate, raw)
                        && BranchNodePageFmt::spec_new().parsable(raw)
                        && raw_page_to_branch_node(raw)
                            == old(self).staged_nodes()[candidate];
                    assert(cache0@.valid_read(candidate, raw));
                    if reserved {
                        assert(borrowed_cache@.valid_read(candidate, raw));
                    }
                    assert(prepared_cache.valid_read(candidate, raw));
                    Cache::State::access_preserves_unwritten_valid_read(
                        prepared_cache,
                        cache@,
                        Map::empty(),
                        writes,
                        candidate,
                        raw,
                    );
                    assert(self.staged_nodes()[candidate]
                        == old(self).staged_nodes()[candidate]);
                }
            }
            assert(self.cache_inv(cache@));
            assert(BranchBulkBuilder::staged_nodes_wf(
                self.staged_nodes(),
            )) by {
                assert forall |candidate: Address|
                    #[trigger] self.staged_nodes().contains_key(candidate)
                    implies {
                        &&& candidate.wf()
                        &&& self.staged_nodes()[candidate].wf()
                        &&& self.staged_nodes()[candidate]
                            .keys_strictly_sorted()
                        &&& !(self.staged_nodes()[candidate] is Auxiliary)
                    } by {
                    if candidate == addr@ {
                        assert(self.staged_nodes()[candidate] == node_view);
                    } else {
                        assert(old(self).staged_nodes()
                            .contains_key(candidate));
                        assert(self.staged_nodes()[candidate]
                            == old(self).staged_nodes()[candidate]);
                    }
                }
            }
            assert(self.wf());
        }
        BulkStageResult::Staged {
            addr,
            prepared_cache: Ghost(prepared_cache),
            writes: Ghost(writes),
            event: Ghost(event),
        }
    }

    pub fn bulk_seal_with_cache(
        &mut self,
        memtable: &MemtableImpl,
        cache: &mut FracCacheImpl,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (result: BulkSealResult)
        requires
            old(self).wf(),
            old(self).bulk_builder is Some,
            old(self).bulk_builder_wf(memtable),
            old(self).builder_ready_to_seal(),
            old(self).mini_allocator.bounded(disk_au_count),
            old(cache).wf(),
            old(cache)@.inv(),
            old(self).cache_inv(old(cache)@),
            0 < disk_page_count as nat,
            disk_page_count as nat == page_count(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BulkSealResult::Sealed {
                    root,
                    aux_ptr,
                    prepared_cache,
                    writes,
                    event,
                    deallocs,
                    branch,
                } => {
                    &&& self.sealed
                    &&& self.root == Some(root)
                    &&& self.bulk_builder is None
                    &&& self.mini_allocator.bounded(disk_au_count)
                    &&& iau_vec_set(deallocs@)
                        <= old(self).mini_allocator.i().all_aus()
                    &&& self.mini_allocator.i().all_aus()
                        == old(self).mini_allocator.i().all_aus()
                            - iau_vec_set(deallocs@)
                    &&& self.sealed_branch@ == Some(branch@)
                    &&& self.sealed_source@
                        == Some(old(self).builder_source_map())
                    &&& event@ == CachedBulkBranchEvent::BulkSeal {
                        root: root@,
                        aux_ptr: iopt_addr(aux_ptr),
                        write_nodes: to_branch_nodes(writes@),
                    }
                    &&& branch@ == old(self)@.staged_branch(
                        root@,
                        to_branch_nodes(writes@),
                    )
                    &&& branch@.valid_sealed_branch()
                    &&& branch@.tight_disk_view_with_summary()
                    &&& branch@.i().i().map
                        == old(self).builder_source_map()
                    &&& CachedBulkBranch::build_next(
                        old(self)@,
                        self@,
                        event@,
                        Set::empty(),
                        iau_vec_set(deallocs@),
                    )
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: Map::empty(),
                            writes: writes@,
                        },
                    )
                    &&& self.cache_inv(cache@)
                },
                BulkSealResult::NeedsAUs
                | BulkSealResult::CacheFull
                | BulkSealResult::Blocked
                | BulkSealResult::InvalidPage => {
                    &&& *self == *old(self)
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost self0 = *self;
        let ghost cache0 = *cache;
        let mut candidate = self.mini_allocator.clone_checked();
        let ghost initial_allocator = candidate.i();
        let root = match candidate.allocate_fresh_addr_checked(
            disk_au_count,
            disk_page_count,
        ) {
            Some(addr) => addr,
            None => return BulkSealResult::NeedsAUs,
        };
        let ghost root_allocator = candidate.i();
        let index_root = match self.bulk_builder.as_ref().unwrap() {
            BulkBuilderImpl::Memtable { memtable } => match memtable.phase {
                crate::implementation::BranchBulkBuilderImpl_v::BranchBulkPhase::ReadyIndexRoot => true,
                _ => false,
            },
            BulkBuilderImpl::Streaming { streaming } => {
                match streaming.phase {
                    StreamingBranchPhase::ReadyIndexRoot => true,
                    _ => false,
                }
            },
        };
        let aux_ptr = if index_root {
            match candidate.allocate_fresh_addr_checked(
                disk_au_count,
                disk_page_count,
            ) {
                Some(addr) => Some(addr),
                None => return BulkSealResult::NeedsAUs,
            }
        } else {
            None
        };
        let ghost bulk_allocator = candidate.i();
        let deallocs = candidate.prune_removable_aus(disk_au_count);
        let summary_aus = candidate.all_aus_vec();
        let ghost summary = iau_vec_set(summary_aus@);

        if index_root {
            let fmt = BranchNodePageFmt::new();
            if summary_aus.len() > fmt.aux_fmt.max_length
                || summary_aus.len() > u8::MAX as usize
            {
                return BulkSealResult::InvalidPage;
            }
        }

        let root_node = match self.bulk_builder.as_ref().unwrap() {
            BulkBuilderImpl::Memtable { memtable } => {
                memtable.root_node(aux_ptr).unwrap()
            },
            BulkBuilderImpl::Streaming { streaming } => {
                streaming.root_node(aux_ptr).unwrap()
            },
        };
        proof {
            assert(self.bulk_builder_wf(memtable));
            if root_node is Leaf {
                if self.has_memtable_builder() {
                    assert(self.memtable_builder().wf(memtable));
                    assert(root_node->keys@.len()
                        == self.memtable_builder().root_leaf@.len());
                    assert(self.memtable_builder().root_leaf@.len()
                        == self.memtable_builder().leaf_partition.total);
                    assert(self.memtable_builder().leaf_partition.node_count == 1);
                    lemma_mul_basics(
                        self.memtable_builder().leaf_partition.capacity as int,
                    );
                    assert(self.memtable_builder().leaf_partition.node_count as int
                        * self.memtable_builder().leaf_partition.capacity as int
                        == self.memtable_builder().leaf_partition.capacity as int);
                    assert(self.memtable_builder().leaf_partition.total
                        <= self.memtable_builder().leaf_partition.capacity);
                    assert(self.memtable_builder().leaf_partition.capacity as int
                        == branch_leaf_capacity_spec());
                } else {
                    assert(self.has_streaming_builder());
                    assert(root_node->keys@.len()
                        <= self.streaming_builder().leaf_tail.capacity);
                }
                assert(root_node->keys@.len()
                    <= branch_leaf_capacity_spec());
                assert(root_node->keys@.len() <= u8::MAX as int) by {

                }
                leaf_branch_node_marshallable(&root_node);
            } else {
                assert(root_node is Index);
                assert(root_node->pivots@.len()
                    <= branch_index_capacity_spec());
                assert(root_node->pivots@.len() <= u8::MAX as int) by {

                }
                index_branch_node_marshallable(&root_node);
            }
        }
        let ghost root_node_view = root_node@;
        let root_page = marshall_branch_node_page(&root_node);
        let ghost root_raw = root_page@;

        if index_root {
            let aux = aux_ptr.unwrap();
            let ghost aux_summary_seq = summary_aus@;
            let aux_node = IBranchNode::Auxiliary {
                summary_aus,
            };
            proof {
                assert(aux_node->summary_aus@ == aux_summary_seq);
                assert(summary == iau_vec_set(aux_summary_seq));
                auxiliary_branch_node_marshallable(&aux_node);
                aux_node.auxiliary_view();
                assert(iau_seq(aux_node->summary_aus@).to_set()
                    == summary) by {
                    assert_sets_equal!(
                        iau_seq(aux_node->summary_aus@).to_set(),
                        summary,
                        au => {
                            if summary.contains(au) {
                                let i = choose |i: int|
                                    0 <= i < aux_summary_seq.len()
                                    && #[trigger] aux_summary_seq[i] as nat
                                        == au;
                                assert(iau_seq(aux_summary_seq)[i] == au);
                                assert(iau_seq(aux_summary_seq).contains(au));
                            }
                            if iau_seq(aux_summary_seq).to_set()
                                .contains(au)
                            {
                                assert(iau_seq(aux_summary_seq).contains(au));
                                let i = iau_seq(aux_summary_seq)
                                    .index_of(au);
                                assert(0 <= i < aux_summary_seq.len());
                                assert(aux_summary_seq[i] as nat == au);
                                assert(summary.contains(au));
                            }
                        }
                    );
                }
                assert(aux_node@ == BranchNode::Auxiliary(summary));
            }
            let ghost aux_node_view = aux_node@;
            let aux_page = marshall_branch_node_page(&aux_node);
            let ghost aux_raw = aux_page@;
            let (mut root_handle, mut aux_handle, prepared_cache_ghost) =
                match cache.prepare_two_for_write(&root, &aux) {
                    PrepareTwoWriteResult::Ready {
                        first_handle,
                        second_handle,
                        prepared_cache,
                    } => (first_handle, second_handle, prepared_cache),
                    PrepareTwoWriteResult::CacheFull => {
                        return BulkSealResult::CacheFull;
                    },
                    PrepareTwoWriteResult::Blocked => {
                        return BulkSealResult::Blocked;
                    },
                };
            let ghost prepared_cache = prepared_cache_ghost@;
            root_handle.rec = root_page;
            aux_handle.rec = aux_page;
            let ghost borrowed_cache = *cache;
            let ghost root_slot = root_handle.idx;
            let ghost aux_slot = aux_handle.idx;
            proof {
                FracCacheImpl::valid_write_handle_model_valid_write(
                    &borrowed_cache,
                    &root,
                    root_handle,
                );
                FracCacheImpl::valid_write_handle_model_valid_write(
                    &borrowed_cache,
                    &aux,
                    aux_handle,
                );
            }
            cache.write_release(&root, root_handle);
            let ghost after_root = *cache;
            proof {
                FracCacheImpl::valid_write_handle_preserved_except(
                    borrowed_cache,
                    after_root,
                    &aux,
                    aux_handle,
                    &root,
                    root_slot,
                );
                FracCacheImpl::valid_write_handle_model_valid_write(
                    &after_root,
                    &aux,
                    aux_handle,
                );
            }
            cache.write_release(&aux, aux_handle);
            proof {
                FracCacheImpl::valid_load_handles_preserved_transitive(
                    borrowed_cache,
                    after_root,
                    *cache,
                );
                FracCacheImpl::valid_writeback_handles_preserved_transitive(
                    borrowed_cache,
                    after_root,
                    *cache,
                );
                FracCacheImpl::two_write_releases_refine_access(
                    prepared_cache,
                    borrowed_cache,
                    after_root,
                    *cache,
                    &root,
                    root_slot,
                    root_raw,
                    &aux,
                    aux_slot,
                    aux_raw,
                );
            }
            let ghost writes = map![root@ => root_raw, aux@ => aux_raw];
            let ghost write_nodes = to_branch_nodes(writes);
            proof {
                let removed = iau_vec_set(deallocs@);
                assert(removed =~= bulk_allocator.removable_aus());
                assert(candidate.i() == bulk_allocator.prune(removed));
                bulk_allocator.prune_removable_all_aus();
                assert(candidate.i().all_aus()
                    =~= bulk_allocator.allocated_aus());
                assert(addrs_closed(
                    self.staged_nodes().dom()
                        .insert(root@).insert(aux@),
                    summary,
                )) by {
                    assert forall |addr: Address|
                        #[trigger] self.staged_nodes().dom()
                            .insert(root@).insert(aux@).contains(addr)
                        implies summary.contains(addr.au) by {
                        if addr != root@ && addr != aux@ {
                            assert(self0.allocated_pages().contains(addr));
                            assert(initial_allocator.allocs[addr.au]
                                .allocated.contains(addr));
                            initial_allocator.allocate_preserves_allocated_page(
                                root@,
                                addr,
                            );
                            root_allocator.allocate_preserves_allocated_page(
                                aux@,
                                addr,
                            );
                        } else if addr == root@ {
                            assert(root_allocator.page_is_allocated(root@));
                            root_allocator.allocate_preserves_allocated_page(
                                aux@,
                                root@,
                            );
                        } else {
                            assert(addr == aux@);
                            assert(bulk_allocator.page_is_allocated(aux@));
                        }
                        assert(bulk_allocator.page_is_allocated(addr));
                        bulk_allocator.prune_removable_preserves_allocated_page(
                            addr,
                        );
                        assert(candidate.i().page_is_allocated(addr));
                        assert(candidate.i().all_aus().contains(addr.au));
                    }
                }
            }
            let ghost branch = match self.bulk_builder {
                Some(BulkBuilderImpl::Memtable { memtable: ref builder }) => {
                    builder.sealed_branch_receipt(
                        memtable,
                        root@,
                        root_node_view,
                        Some(aux@),
                        summary,
                    )
                },
                Some(BulkBuilderImpl::Streaming { ref streaming }) => {
                    streaming.sealed_branch_receipt(
                        root@,
                        root_node_view,
                        Some(aux@),
                        summary,
                    )
                },
                None => {
                    assert(false);
                    arbitrary()
                },
            };
            let ghost event = CachedBulkBranchEvent::BulkSeal {
                root: root@,
                aux_ptr: Some(aux@),
                write_nodes,
            };
            self.root = Some(root);
            self.root_node = Some(root_node);
            self.mini_allocator = candidate;
            self.sealed = true;
            self.bulk_builder = None;
            self.sealed_branch = Ghost(Some(branch));
            self.sealed_source = Ghost(Some(self0.builder_source_map()));
            proof {
                assert(write_nodes[root@] == root_node_view);
                assert(write_nodes[aux@] == aux_node_view);
                assert(write_nodes.dom() == set![root@, aux@]) by {
                    assert_sets_equal!(write_nodes.dom(), set![root@, aux@], addr => {});
                }
                assert(branch == self0@.staged_branch(root@, write_nodes)) by {


                    assert_maps_equal!(
                        branch.disk_view.entries,
                        self0.staged_nodes()
                            .union_prefer_right(write_nodes),
                        addr => {
                            if addr == root@ {
                                assert(branch.disk_view.entries[addr]
                                    == root_node_view);
                                assert(write_nodes[addr]
                                    == root_node_view);
                            } else if addr == aux@ {
                                assert(aux_node_view
                                    == BranchNode::Auxiliary(summary));
                                assert(branch.disk_view.entries[aux@]
                                    == BranchNode::Auxiliary(summary));
                                assert(branch.disk_view.entries[addr]
                                    == aux_node_view);
                                assert(write_nodes[addr]
                                    == aux_node_view);
                            } else {
                                assert(!write_nodes.contains_key(addr));
                            }
                        }
                    );
                }
                assert(initial_allocator == self0.mini_allocator.i());
                assert(root_allocator
                    == initial_allocator.allocate(root@));
                assert(bulk_allocator
                    == root_allocator.allocate(aux@));
                let removed = iau_vec_set(deallocs@);
                assert(removed =~= bulk_allocator.removable_aus());
                assert(candidate.i() == bulk_allocator.prune(removed));
                bulk_allocator.prune_preserves_wf(removed);
                assert(summary
                    == bulk_allocator.all_aus() - removed);
                assert forall |addr: Address|
                    #[trigger] branch.disk_view.entries.contains_key(addr)
                    implies exists |raw: RawPage|
                        cache@.valid_read(addr, raw)
                        && BranchNodePageFmt::spec_new().parsable(raw)
                        && raw_page_to_branch_node(raw)
                            == branch.disk_view.entries[addr] by {
                    if addr == root@ {
                        assert(cache@.valid_read(root@, root_raw));
                        assert(BranchNodePageFmt::spec_new()
                            .parsable(root_raw));
                        assert(raw_page_to_branch_node(root_raw)
                            == root_node_view);
                    } else if addr == aux@ {
                        assert(cache@.valid_read(aux@, aux_raw));
                        assert(BranchNodePageFmt::spec_new()
                            .parsable(aux_raw));
                        assert(raw_page_to_branch_node(aux_raw)
                            == aux_node_view);
                    } else {
                        assert(self0.staged_nodes().contains_key(addr));
                        let raw = choose |raw: RawPage|
                            cache0@.valid_read(addr, raw)
                            && BranchNodePageFmt::spec_new().parsable(raw)
                            && raw_page_to_branch_node(raw)
                                == self0.staged_nodes()[addr];
                        assert(cache0@.valid_read(addr, raw));
                        assert(prepared_cache.valid_read(addr, raw));
                        Cache::State::access_preserves_unwritten_valid_read(
                            prepared_cache,
                            cache@,
                            Map::empty(),
                            writes,
                            addr,
                            raw,
                        );
                        assert(branch.disk_view.entries[addr]
                            == self0.staged_nodes()[addr]);
                    }
                }

                assert(self.wf());
                assert(self.cache_inv(cache@));
            }
            return BulkSealResult::Sealed {
                root,
                aux_ptr,
                prepared_cache: Ghost(prepared_cache),
                writes: Ghost(writes),
                event: Ghost(event),
                deallocs,
                branch: Ghost(branch),
            };
        }

        let ghost borrowed_cache;
        let ghost prepared_cache;
        let mut handle = if cache.contains_addr(&root) {
            match cache.fetch(&root, false) {
                FetchErrorCode::Success { slot_handle } => {
                    proof {
                        borrowed_cache = *cache;
                        prepared_cache = cache0@;
                        FracCacheImpl::valid_write_handle_model_entry(
                            cache,
                            &root,
                            slot_handle,
                        );
                    }
                    slot_handle
                },
                FetchErrorCode::CacheFull => {
                    return BulkSealResult::CacheFull;
                },
                FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                    return BulkSealResult::Blocked;
                },
                FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                    proof { assert(false); }
                    return BulkSealResult::Blocked;
                },
            }
        } else {
            match cache.reserve_for_write_absent(&root) {
                ReserveWriteResult::Reserved { slot_handle } => {
                    proof {
                        borrowed_cache = *cache;
                        prepared_cache = cache@;
                    }
                    slot_handle
                },
                ReserveWriteResult::CacheFull => {
                    return BulkSealResult::CacheFull;
                },
            }
        };
        let ghost slot = handle.idx;
        handle.rec = root_page;
        cache.write_release(&root, handle);
        let ghost writes = map![root@ => root_raw];
        let ghost write_nodes = to_branch_nodes(writes);
        proof {
            if self.has_streaming_builder() {
                self.streaming_builder().ready_leaf_has_no_staged_nodes();
            }
            assert(self.staged_nodes()
                == LoadedBranch::empty());
            assert(self0.allocated_pages().is_empty());
            assert(initial_allocator.allocated_aus().is_empty()) by {
                assert_sets_equal!(
                    initial_allocator.allocated_aus(),
                    Set::empty(),
                    au => {
                        if initial_allocator.allocated_aus().contains(au) {
                            assert(!initial_allocator.allocs[au]
                                .has_no_allocated_pages());
                            assert(initial_allocator.allocs[au].allocated
                                != Set::<Address>::empty());
                            assert(exists |addr: Address|
                                initial_allocator.allocs[au]
                                    .allocated.contains(addr)) by {
                                if !(exists |addr: Address|
                                    initial_allocator.allocs[au]
                                        .allocated.contains(addr))
                                {
                                    assert(initial_allocator.allocs[au]
                                        .allocated =~=
                                            Set::<Address>::empty());
                                }
                            }
                            let addr = choose |addr: Address|
                                initial_allocator.allocs[au]
                                    .allocated.contains(addr);
                            assert(initial_allocator.allocs[au]
                                .allocated.contains(addr));
                            assert(self0.allocated_pages().contains(addr));
                        }
                    }
                );
            }
            initial_allocator.allocate_allocated_aus(root@);
            assert(root_allocator.allocated_aus()
                =~= set![root@.au]);
            let removed = iau_vec_set(deallocs@);
            assert(removed =~= bulk_allocator.removable_aus());
            assert(candidate.i() == bulk_allocator.prune(removed));
            bulk_allocator.prune_removable_all_aus();
            assert(candidate.i().all_aus()
                =~= bulk_allocator.allocated_aus());
            assert(summary == set![root@.au]) by {
                assert_sets_equal!(summary, set![root@.au], au => {});
            }
        }
        let ghost branch = match self.bulk_builder {
            Some(BulkBuilderImpl::Memtable { memtable: ref builder }) => {
                builder.sealed_branch_receipt(
                    memtable,
                    root@,
                    root_node_view,
                    None,
                    summary,
                )
            },
            Some(BulkBuilderImpl::Streaming { ref streaming }) => {
                streaming.sealed_branch_receipt(
                    root@,
                    root_node_view,
                    None,
                    summary,
                )
            },
            None => {
                assert(false);
                arbitrary()
            },
        };
        let ghost event = CachedBulkBranchEvent::BulkSeal {
            root: root@,
            aux_ptr: None,
            write_nodes,
        };
        self.root = Some(root);
        self.root_node = Some(root_node);
        self.mini_allocator = candidate;
        self.sealed = true;
        self.bulk_builder = None;
        self.sealed_branch = Ghost(Some(branch));
        self.sealed_source = Ghost(Some(self0.builder_source_map()));
        proof {
            if prepared_cache == cache0@ {
                reveal(Cache::State::next);
                reveal(Cache::State::next_by);
                assert(Cache::State::next_by(
                    cache0@,
                    prepared_cache,
                    Cache::Label::Internal,
                    Cache::Step::noop(),
                ));
                Cache::State::access_from_borrowed_write_slot(
                    prepared_cache,
                    borrowed_cache@,
                    cache@,
                    Map::empty(),
                    root@,
                    slot,
                    root_raw,
                );
            }
            assert(write_nodes[root@] == root_node_view);
            assert(write_nodes.dom() == set![root@]) by {
                assert_sets_equal!(write_nodes.dom(), set![root@], addr => {});
            }
            assert(branch == self0@.staged_branch(root@, write_nodes)) by {


                assert_maps_equal!(
                    branch.disk_view.entries,
                    self0.staged_nodes().union_prefer_right(write_nodes),
                    addr => {}
                );
            }
            assert(initial_allocator == self0.mini_allocator.i());
            assert(root_allocator == initial_allocator.allocate(root@));
            assert(bulk_allocator == root_allocator);
            let removed = iau_vec_set(deallocs@);
            assert(removed =~= bulk_allocator.removable_aus());
            assert(candidate.i() == bulk_allocator.prune(removed));
            bulk_allocator.prune_preserves_wf(removed);
            assert(summary == bulk_allocator.all_aus() - removed);

            assert(self.wf());
            assert(self.cache_inv(cache@));
        }
        BulkSealResult::Sealed {
            root,
            aux_ptr,
            prepared_cache: Ghost(prepared_cache),
            writes: Ghost(writes),
            event: Ghost(event),
            deallocs,
            branch: Ghost(branch),
        }
    }

    /* Old single-leaf construction retained for reference. The live path uses
     * stage_bulk_page_with_cache followed by bulk_seal_with_cache.
    /* Preserved in WipBranchImpl_v for the mutable branch-as-memtable path.
    pub fn initialize_leaf_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        contents: WipLeafContents,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (result: BulkBranchInitializeResult)
        requires
            old(self).wf(),
            !old(self).sealed,
            old(self).root is None,
            old(self).bulk_builder is None,
            old(self).mini_allocator.bounded(disk_au_count),
            old(self).mini_allocator.i().allocated_aus().is_empty(),
            old(cache).wf(),
            contents.keys@.len() > 0,
            contents.keys@.len() == contents.msgs@.len(),
            Key::is_strictly_sorted(contents.keys@),
            0 < disk_page_count as nat,
            disk_page_count as nat == page_count(),
        ensures
            self.wf(),
            self.bulk_builder is None,
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BulkBranchInitializeResult::Initialized {
                    root,
                    prepared_cache,
                    writes,
                    event,
                } => {
                    &&& event@ == CachedBulkBranchEvent::Initialize {
                        init_root: root@,
                        keys: contents.keys@,
                        msgs: contents.msgs@,
                        write_nodes: to_branch_nodes(writes@),
                    }
                    &&& writes@.dom() == set![root@]
                    &&& self.cache_inv(cache@)
                    &&& self.root_node is Some
                    &&& self.root_node->0@
                        == crate::allocation_layer::BranchTypes_v::BranchNode::Leaf {
                            keys: contents.keys@,
                            msgs: contents.msgs@,
                        }
                    &&& CachedBulkBranch::build_next(
                        old(self)@,
                        self@,
                        event@,
                        Set::empty(),
                        Set::empty(),
                    )
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: Map::empty(),
                            writes: writes@,
                        },
                    )
                },
                BulkBranchInitializeResult::NeedsAUs
                | BulkBranchInitializeResult::CacheFull
                | BulkBranchInitializeResult::Blocked => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        if !self.mini_allocator.is_allocation_ready() {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BulkBranchInitializeResult::NeedsAUs;
        }
        let root = self.mini_allocator.peek_next_addr();
        if root.page >= disk_page_count {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BulkBranchInitializeResult::Blocked;
        }
        let fmt = BranchNodePageFmt::new();
        if contents.keys.len() > fmt.leaf_fmt.max_length
            || contents.keys.len() > u8::MAX as usize
        {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BulkBranchInitializeResult::Blocked;
        }
        if cache.contains_addr(&root) {
            proof {
                assert(cache@ == old(cache)@);
            }
            return BulkBranchInitializeResult::Blocked;
        }
        let ghost cache_before_reserve = *cache;
        let mut handle = match cache.reserve_for_write_absent(&root) {
            ReserveWriteResult::Reserved { slot_handle } => slot_handle,
            ReserveWriteResult::CacheFull => {
                return BulkBranchInitializeResult::CacheFull;
            },
        };
        let ghost prepared_cache = *cache;
        let node = IBranchNode::Leaf {
            keys: contents.keys,
            msgs: contents.msgs,
        };
        proof {
            assert(node.wf());
            assert(node@.wf()) by {
                assert(node@ == crate::allocation_layer::BranchTypes_v::BranchNode::Leaf {
                    keys: node->keys@,
                    msgs: node->msgs@,
                });
            }
            assert(node@.keys_strictly_sorted());
            assert(fmt == BranchNodePageFmt::spec_new());
            leaf_branch_node_marshallable(&node);
        }
        let ghost node_view = node@;
        let ghost keys_view = node->keys@;
        let ghost msgs_view = node->msgs@;
        let page = marshall_branch_node_page(&node);
        let ghost page_view = page@;
        let ghost writes = map![root@ => page_view];
        let allocated = self.mini_allocator.allocate_fresh_addr_checked(
            disk_au_count,
            disk_page_count,
        );
        proof {
            assert(allocated is Some);
            assert(allocated.unwrap() == root);
        }
        self.root = Some(root);
        self.root_node = Some(node);
        handle.rec = page;
        proof {
            assert(cache.valid_write_handle(&root, handle));
            assert(cache@.valid_write(root@));
        }
        cache.write_release(&root, handle);
        let ghost event = CachedBulkBranchEvent::Initialize {
            init_root: root@,
            keys: keys_view,
            msgs: msgs_view,
            write_nodes: to_branch_nodes(writes),
        };
        proof {
            assert(cache_before_reserve@ == old(cache)@);
            assert(Cache::State::next(
                cache_before_reserve@,
                prepared_cache@,
                Cache::Label::Internal,
            ));
            assert(Cache::State::next(
                prepared_cache@,
                cache@,
                Cache::Label::Access {
                    reads: Map::empty(),
                    writes,
                },
            ));
            assert(to_branch_nodes(writes)
                == loaded_initialize_write_nodes(
                    root@,
                    keys_view,
                    msgs_view,
                )) by {
                assert forall |addr: Address|
                    #[trigger] to_branch_nodes(writes).contains_key(addr)
                    == loaded_initialize_write_nodes(
                        root@,
                        keys_view,
                        msgs_view,
                    ).contains_key(addr) by {}
                assert forall |addr: Address|
                    to_branch_nodes(writes).contains_key(addr)
                    implies #[trigger] to_branch_nodes(writes)[addr]
                        == loaded_initialize_write_nodes(
                            root@,
                            keys_view,
                            msgs_view,
                        )[addr] by {
                    assert(addr == root@);
                    assert(crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node(
                        page_view,
                    ) == node_view);
                }
            }
            let branch_label = CachedBranch::Label::Initialize {
                mini_allocator: old(self).mini_allocator.i(),
                init_root: root@,
                keys: self.root_node->0->keys@,
                msgs: self.root_node->0->msgs@,
                write_nodes: to_branch_nodes(writes),
            };
            assert(CachedBranch::State::initialize_branch(
                old(self)@.branch,
                self@.branch,
                branch_label,
            )) by {

            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                old(self)@.branch,
                self@.branch,
                branch_label,
                CachedBranch::Step::initialize_branch(),
            ));
            assert(CachedBranch::State::next(
                old(self)@.branch,
                self@.branch,
                branch_label,
            ));

            assert(cache@.valid_read(root@, page_view)) by {
                reveal(Cache::State::next);
                reveal(Cache::State::next_by);

            }
            assert(self.cache_inv(cache@)) by {
                assert(BranchNodePageFmt::spec_new().parsable(page_view));
                assert(raw_page_to_branch_node(page_view)
                    == self.root_node->0@);
            }
            assert(self.wf());
        }
        BulkBranchInitializeResult::Initialized {
            root,
            prepared_cache: Ghost(prepared_cache@),
            writes: Ghost(writes),
            event: Ghost(event),
        }
    }

    pub fn seal_leaf_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
    ) -> (result: BulkBranchSealResult)
        requires
            old(self).wf(),
            !old(self).sealed,
            old(self).root is Some,
            old(self).root_node->0 is Leaf,
            old(self).cache_inv(old(cache)@),
            old(self).mini_allocator.i().all_aus()
                == old(self).mini_allocator.i().allocated_aus(),
            old(cache).wf(),
        ensures
            self.wf(),
            self.root_node == old(self).root_node,
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BulkBranchSealResult::Sealed { reads, event } => {
                    &&& event@ == CachedBulkBranchEvent::Seal {
                        aux_ptr: None,
                        read_nodes: to_branch_nodes(reads@),
                        write_nodes: Map::empty(),
                    }
                    &&& self.sealed
                    &&& self.cache_inv(cache@)
                    &&& CachedBulkBranch::build_next(
                        old(self)@,
                        self@,
                        event@,
                        Set::empty(),
                        Set::empty(),
                    )
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                BulkBranchSealResult::CacheFull
                | BulkBranchSealResult::Blocked
                | BulkBranchSealResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let root = self.root.unwrap();
        let ghost cache0 = *cache;
        let mut handle = match cache.fetch(&root, false) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::CacheFull => {
                return BulkBranchSealResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BulkBranchSealResult::Blocked;
            },
            FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                proof { assert(false); }
                return BulkBranchSealResult::Blocked;
            },
        };
        let ghost raw = handle.rec@;
        let ghost fetched_slot = handle.idx;
        let fmt = BranchNodePageFmt::new();
        let all_slice = Slice::all(&handle.rec);
        let parsed = fmt.try_parse(&all_slice, &handle.rec);
        proof {
            let expected_raw = choose |candidate: RawPage|
                cache0@.valid_read(root@, candidate)
                && BranchNodePageFmt::spec_new().parsable(candidate)
                && raw_page_to_branch_node(candidate)
                    == old(self).root_node->0@;
            assert(cache0@.valid_read(root@, raw));
            Cache::State::valid_read_unique(
                cache0@,
                root@,
                raw,
                expected_raw,
            );
            assert(raw == expected_raw);
            assert(fmt == BranchNodePageFmt::spec_new());
            assert(all_slice@.i(handle.rec@) == raw);
            assert(parsed is Some);
            assert(parsed.unwrap().parsedv() == fmt.parse(raw));
            assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
            assert(parsed.unwrap()@ == old(self).root_node->0@);
            assert(parsed.unwrap() is Leaf);
        }
        let node = match parsed {
            Some(node) => node,
            None => {
                proof { assert(false); }
                cache.handle_release(&root, handle);
                return BulkBranchSealResult::InvalidPage;
            },
        };
        cache.handle_release(&root, handle);
        let ghost reads = map![root@ => raw];
        let ghost event = CachedBulkBranchEvent::Seal {
            aux_ptr: None,
            read_nodes: to_branch_nodes(reads),
            write_nodes: Map::empty(),
        };
        self.sealed = true;
        proof {
            assert(cache@ == cache0@) by {
                assert(cache0@.entries
                    == cache@.entries.insert(
                        fetched_slot,
                        crate::implementation::Cache_v::Entry::Filled {
                            addr: root@,
                            data: raw,
                        },
                    ));
                assert(cache@.entries == cache0@.entries);
                assert(cache@.lookup_map == cache0@.lookup_map);
                assert(cache@.status_map == cache0@.status_map);
            }
            assert(to_branch_nodes(reads)[root@] == node@);
            assert(node@ == old(self).root_node->0@);
            assert(to_branch_nodes(reads)[root@] is Leaf);
            assert(old(self).mini_allocator.i().removable_aus().is_empty()) by {
                assert forall |au: crate::disk::GenericDisk_v::AU|
                    #[trigger] old(self).mini_allocator.i()
                        .removable_aus().contains(au)
                    implies false by {
                    assert(old(self).mini_allocator.i().all_aus().contains(au));
                    assert(old(self).mini_allocator.i().allocated_aus().contains(au));
                    assert(old(self).mini_allocator.i().allocs[au]
                        .has_no_allocated_pages());
                    assert(!old(self).mini_allocator.i().allocs[au]
                        .has_no_allocated_pages());
                }
            }
            assert(crate::implementation::CachedBranch_v::loaded_line_wf(
                to_branch_nodes(reads),
                root@,
            ));
            assert(crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
                root@,
                to_branch_nodes(reads),
                None,
                old(self).mini_allocator.i().allocated_aus(),
            ) == Map::<
                Address,
                crate::allocation_layer::BranchTypes_v::BranchNode,
            >::empty());
            let branch_label = CachedBranch::Label::Seal {
                mini_allocator: old(self).mini_allocator.i(),
                aux_ptr: None,
                read_nodes: to_branch_nodes(reads),
                write_nodes: Map::empty(),
            };
            assert(CachedBranch::State::seal_step(
                old(self)@.branch,
                self@.branch,
                branch_label,
            )) by {

            }
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            assert(CachedBranch::State::next_by(
                old(self)@.branch,
                self@.branch,
                branch_label,
                CachedBranch::Step::seal_step(),
            ));
            assert(CachedBranch::State::next(
                old(self)@.branch,
                self@.branch,
                branch_label,
            ));
            assert(old(self).mini_allocator.i().prune(Set::empty())
                == old(self).mini_allocator.i()) by {

                assert(old(self).mini_allocator.i().allocs.remove_keys(Set::empty())
                    =~= old(self).mini_allocator.i().allocs);
            }

            Cache::State::access_read_only_from_valid_reads(cache0@, reads);
            assert(self.cache_inv(cache@));
            assert(self.wf());
        }
        BulkBranchSealResult::Sealed {
            reads: Ghost(reads),
            event: Ghost(event),
        }
    }

    */

    */

    pub fn read_sealed_leaf(
        &self,
        cache: &mut FracCacheImpl,
    ) -> (result: BulkBranchReadResult)
        requires
            self.wf(),
            self.sealed,
            self.root is Some,
            self.cache_inv(old(cache)@),
            old(cache).wf(),
        ensures
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BulkBranchReadResult::Read { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.dom() == set![self.root.unwrap()@]
                    &&& to_branch_nodes(reads@)[self.root.unwrap()@]
                        == self.root_node->0@
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                BulkBranchReadResult::CacheFull
                | BulkBranchReadResult::Blocked
                | BulkBranchReadResult::InvalidPage => {
                    cache@ == old(cache)@
                },
            },
    {
        let root = self.root.unwrap();
        let ghost cache0 = *cache;
        let handle = match cache.fetch(&root, false) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::CacheFull => {
                return BulkBranchReadResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BulkBranchReadResult::Blocked;
            },
            FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                proof { assert(false); }
                return BulkBranchReadResult::Blocked;
            },
        };
        let ghost raw = handle.rec@;
        let ghost fetched_slot = handle.idx;
        let fmt = BranchNodePageFmt::new();
        let all_slice = Slice::all(&handle.rec);
        let parsed = fmt.try_parse(&all_slice, &handle.rec);
        proof {
            let expected_raw = choose |candidate: RawPage|
                cache0@.valid_read(root@, candidate)
                && BranchNodePageFmt::spec_new().parsable(candidate)
                && raw_page_to_branch_node(candidate) == self.root_node->0@;
            assert(cache0@.valid_read(root@, raw));
            Cache::State::valid_read_unique(
                cache0@,
                root@,
                raw,
                expected_raw,
            );
            assert(raw == expected_raw);
            assert(fmt == BranchNodePageFmt::spec_new());
            assert(all_slice@.i(handle.rec@) == raw);
            assert(parsed is Some);
            assert(parsed.unwrap().parsedv() == fmt.parse(raw));
            assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
            assert(parsed.unwrap()@ == self.root_node->0@);
        }
        if parsed.is_none() {
            proof { assert(false); }
            cache.handle_release(&root, handle);
            return BulkBranchReadResult::InvalidPage;
        }
        cache.handle_release(&root, handle);
        let ghost reads = map![root@ => raw];
        proof {
            assert(cache@ == cache0@) by {
                assert(cache0@.entries
                    == cache@.entries.insert(
                        fetched_slot,
                        crate::implementation::Cache_v::Entry::Filled {
                            addr: root@,
                            data: raw,
                        },
                    ));
                assert(cache@.entries == cache0@.entries);
                assert(cache@.lookup_map == cache0@.lookup_map);
                assert(cache@.status_map == cache0@.status_map);
            }
            assert(to_branch_nodes(reads)[root@] == self.root_node->0@);
            Cache::State::access_read_only_from_valid_reads(cache0@, reads);
        }
        BulkBranchReadResult::Read { reads: Ghost(reads) }
    }

    pub proof fn sealed_branch_reads(
        &self,
        cache: Cache::State,
    ) -> (reads: Map<Address, RawPage>)
        requires
            self.wf(),
            self.sealed_branch@ is Some,
            self.cache_inv(cache),
        ensures
            reads.dom()
                == self.sealed_branch@.unwrap().disk_view.entries.dom(),
            forall |addr: Address|
                #[trigger] reads.contains_key(addr)
                ==> cache.valid_read(addr, reads[addr]),
            to_branch_nodes(reads)
                == self.sealed_branch@.unwrap().disk_view.entries,
    {
        let branch = self.sealed_branch@.unwrap();
        let reads = Map::new(
            |addr: Address| branch.disk_view.entries.contains_key(addr),
            |addr: Address| Self::sealed_branch_raw(
                cache,
                branch,
                addr,
            ),
        );
        assert(reads.dom() == branch.disk_view.entries.dom());
        assert forall |addr: Address|
            #[trigger] reads.contains_key(addr)
            implies {
                &&& cache.valid_read(addr, reads[addr])
                &&& BranchNodePageFmt::spec_new()
                    .parsable(reads[addr])
                &&& raw_page_to_branch_node(reads[addr])
                    == branch.disk_view.entries[addr]
            } by {
            let raw = Self::sealed_branch_raw(cache, branch, addr);
            assert(exists |candidate: RawPage|
                cache.valid_read(addr, candidate)
                && BranchNodePageFmt::spec_new().parsable(candidate)
                && raw_page_to_branch_node(candidate)
                    == branch.disk_view.entries[addr]);
            assert(reads[addr] == raw);
            assert(cache.valid_read(addr, raw));
            assert(BranchNodePageFmt::spec_new().parsable(raw));
            assert(raw_page_to_branch_node(raw)
                == branch.disk_view.entries[addr]);
        }
        assert(to_branch_nodes(reads).dom()
            == branch.disk_view.entries.dom()) by {
            assert_sets_equal!(
                to_branch_nodes(reads).dom(),
                branch.disk_view.entries.dom(),
                addr => {}
            );
        }
        assert_maps_equal!(
            to_branch_nodes(reads),
            branch.disk_view.entries,
            addr => {
                if branch.disk_view.entries.contains_key(addr) {
                    assert(reads.contains_key(addr));
                    let raw = Self::sealed_branch_raw(
                        cache,
                        branch,
                        addr,
                    );
                    assert(exists |candidate: RawPage|
                        cache.valid_read(addr, candidate)
                        && BranchNodePageFmt::spec_new()
                            .parsable(candidate)
                        && raw_page_to_branch_node(candidate)
                            == branch.disk_view.entries[addr]);
                    assert(reads[addr] == raw);
                    assert(raw_page_to_branch_node(raw)
                        == branch.disk_view.entries[addr]);
                }
                if to_branch_nodes(reads).contains_key(addr) {
                    assert(branch.disk_view.entries.contains_key(addr));
                    assert(raw_page_to_branch_node(reads[addr])
                        == branch.disk_view.entries[addr]);
                }
            }
        );
        reads
    }

    pub proof fn sealed_branch_reads_valid(
        &self,
        reads: Map<Address, RawPage>,
    )
        requires
            self.wf(),
            self.sealed_branch@ is Some,
            to_branch_nodes(reads)
                == self.sealed_branch@.unwrap().disk_view.entries,
        ensures
            valid_loaded_sealed_branch(
                self.root.unwrap()@,
                self.mini_allocator.i().all_aus(),
                to_branch_nodes(reads),
            ),
            loaded_sealed_branch(
                self.root.unwrap()@,
                to_branch_nodes(reads).restrict(
                    crate::implementation::CachingDisk_v::addresses_in_aus(
                        self.mini_allocator.i().all_aus(),
                    ),
                ),
            ) == self.sealed_branch@.unwrap(),
    {
        let branch = self.sealed_branch@.unwrap();
        let summary = self.mini_allocator.i().all_aus();
        let nodes = to_branch_nodes(reads);
        assert(branch.root == self.root.unwrap()@);
        assert(branch.get_summary() == summary);
        assert(branch.disk_view.entries.dom() == branch.full_repr()) by {
            assert(branch.disk_view.representation()
                == branch.full_repr());
        }
        assert(nodes.restrict(
            crate::implementation::CachingDisk_v::addresses_in_aus(
                summary,
            ),
        ) == nodes) by {
            assert_maps_equal!(
                nodes.restrict(
                    crate::implementation::CachingDisk_v::addresses_in_aus(
                        summary,
                    ),
                ),
                nodes,
                addr => {
                    if nodes.contains_key(addr) {
                        assert(branch.full_repr().contains(addr));
                        assert(summary.contains(addr.au));
                        assert(crate::implementation::CachingDisk_v::addresses_in_aus(
                            summary,
                        ).contains(addr));
                    }
                }
            );
        }
        assert(loaded_sealed_branch(
            self.root.unwrap()@,
            nodes.restrict(
                crate::implementation::CachingDisk_v::addresses_in_aus(
                    summary,
                ),
            ),
        ) == branch);
        assert(valid_loaded_sealed_branch(
            self.root.unwrap()@,
            summary,
            nodes,
        ));
    }

    pub proof fn sealed_leaf_reads_valid(
        &self,
        reads: Map<Address, RawPage>,
        buffer: SimpleBuffer,
    )
        requires
            self.wf(),
            self.sealed,
            self.root is Some,
            self.represents_buffer(buffer),
            self.mini_allocator.i().all_aus()
                == set![self.root.unwrap()@.au],
            reads.dom() == set![self.root.unwrap()@],
            to_branch_nodes(reads)[self.root.unwrap()@]
                == self.root_node->0@,
        ensures
            valid_loaded_sealed_branch(
                self.root.unwrap()@,
                self.mini_allocator.i().all_aus(),
                to_branch_nodes(reads),
            ),
            loaded_sealed_branch(
                self.root.unwrap()@,
                to_branch_nodes(reads),
            ).i().i() == buffer,
    {
        let root = self.root.unwrap()@;
        let summary = self.mini_allocator.i().all_aus();
        let nodes = to_branch_nodes(reads);
        let restricted = nodes.restrict(
            crate::implementation::CachingDisk_v::addresses_in_aus(summary),
        );
        assert(restricted == nodes) by {
            assert_maps_equal!(restricted, nodes, addr => {
                if nodes.contains_key(addr) {
                    assert(addr == root);
                    assert(summary.contains(addr.au));
                }
            });
        }
        let branch = loaded_sealed_branch(root, nodes);
        let ranking = map![root => 1nat];
        assert(branch.disk_view.entries == map![root => self.root_node->0@]) by {
            assert_maps_equal!(
                branch.disk_view.entries,
                map![root => self.root_node->0@],
                addr => {}
            );
        }
        assert(branch.disk_view.wf()) by {
            assert forall |addr: Address|
                #[trigger] branch.disk_view.entries.contains_key(addr)
                implies branch.disk_view.entries[addr].wf() by {
                assert(addr == root);
            }
            assert forall |addr: Address|
                #[trigger] branch.disk_view.entries.contains_key(addr)
                implies branch.disk_view.node_has_valid_child_address(
                    branch.disk_view.entries[addr],
                ) by {
                assert(addr == root);
                assert(branch.disk_view.entries[addr] is Leaf);
            }
        }
        assert(branch.wf());
        assert(branch.valid_ranking(ranking)) by {
            assert(branch.disk_view.valid_ranking(ranking)) by {
                assert forall |addr: Address|
                    #[trigger] ranking.contains_key(addr)
                        && branch.disk_view.entries.contains_key(addr)
                    implies branch.disk_view.node_children_respects_rank(
                        ranking,
                        addr,
                    ) by {
                    assert(addr == root);
                    assert(branch.disk_view.entries[addr] is Leaf);
                }
            }
        }
        assert(branch.acyclic());
        assert(branch.keys_strictly_sorted_internal(branch.the_ranking()));
        assert(branch.all_keys_in_range_internal(branch.the_ranking()));
        assert(branch.inv());
        assert(branch.sealed_root());
        assert(branch.get_summary() == set![root.au]);
        assert(branch.get_summary() == summary);
        assert(crate::disk::GenericDisk_v::addrs_closed(
            branch.full_repr(),
            branch.get_summary(),
        ));
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            branch.disk_view.entries,
            branch.get_summary(),
        ) =~= branch.full_repr());
        assert(branch.valid_sealed_branch());
        assert(valid_loaded_sealed_branch(root, summary, nodes));
        assert(branch.i() == (PivotNode::Leaf {
            keys: self.root_node->0@->keys,
            msgs: self.root_node->0@->msgs,
        }));
        assert(branch.i().i() == buffer);
    }
}

impl View for BulkBranchImpl {
    type V = CachedBulkBranch;

    open spec fn view(&self) -> Self::V {
        self.i()
    }
}

pub open spec fn bulk_branch_views(
    branches: Seq<BulkBranchImpl>,
) -> Seq<CachedBulkBranch> {
    branches.map(|i: int, branch: BulkBranchImpl| branch@)
}

pub open spec fn bulk_branches_wf(branches: Seq<BulkBranchImpl>) -> bool {
    forall |i: int| 0 <= i < branches.len()
        ==> (#[trigger] branches[i]).wf()
}

pub open spec fn bulk_builders_wf(
    branches: Seq<BulkBranchImpl>,
    memtable: &MemtableImpl,
) -> bool {
    forall |i: int| 0 <= i < branches.len()
        ==> (#[trigger] branches[i]).bulk_builder_wf(memtable)
}

pub open spec fn no_bulk_builders(
    branches: Seq<BulkBranchImpl>,
) -> bool {
    forall |i: int| 0 <= i < branches.len()
        ==> (#[trigger] branches[i]).bulk_builder is None
}

} // verus!
