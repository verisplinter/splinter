// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_sets_equal};

use crate::disk::GenericDisk_v::{Address, page_count, to_aus};
use crate::implementation::AuPoolImpl_v::iau_vec_set;
use crate::implementation::BetreePageImpl_v::betree_addr_for_au;
use crate::implementation::BetreeSplitWriteImpl_v::iaddr_views;
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::implementation::BetreePageImpl_v::{
    bounded_betree_node_marshallable, marshall_betree_node_page,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranchBetree_v::flush_memtable_writes;
use crate::implementation::CachingDiskBranchBetree_v::to_betree_nodes;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle, ReserveWriteResult,
};
use crate::marshalling::IBetreeNodeFormat_v::{
    BetreeNodePageFmt, raw_page_to_betree_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::{IAddress, IAU};

verus! {

pub fn compaction_destination_addrs(
    aus: &Vec<IAU>,
) -> (out: (IAddress, Vec<IAddress>))
    requires
        aus@.len() > 0,
        MiniAllocatorImpl::iau_seq_unique(aus@),
        0 < page_count(),
    ensures
        out.0.au == aus@[0],
        out.0.page == 0,
        out.0@.wf(),
        out.1@.len() == aus@.len() - 1,
        forall |i: int| 0 <= i < out.1@.len() ==> {
            &&& (#[trigger] out.1@[i]).au == aus@[i + 1]
            &&& out.1@[i].page == 0
            &&& out.1@[i]@.wf()
        },
        crate::disk::GenericDisk_v::
            seq_addrs_disjoint_aus(iaddr_views(out.1@)),
        !crate::allocation_layer::AllocationBranchBetree_v::
            seq_addrs_to_aus(iaddr_views(out.1@)).contains(out.0@.au),
        to_aus(iaddr_views(out.1@).to_set()).insert(out.0@.au)
            =~= iau_vec_set(aus@),
{
    let first = betree_addr_for_au(aus[0]);
    let mut rest = Vec::<IAddress>::new();
    let mut index = 1usize;
    while index < aus.len()
        invariant
            aus@.len() > 0,
            MiniAllocatorImpl::iau_seq_unique(aus@),
            0 < page_count(),
            1 <= index <= aus.len(),
            rest@.len() == index - 1,
            forall |i: int| 0 <= i < rest@.len() ==> {
                &&& (#[trigger] rest@[i]).au == aus@[i + 1]
                &&& rest@[i].page == 0
                &&& rest@[i]@.wf()
            },
        decreases aus.len() - index,
    {
        rest.push(betree_addr_for_au(aus[index]));
        index += 1;
    }
    proof {
        assert forall |i: int, j: int|
            0 <= i < rest@.len()
            && 0 <= j < rest@.len()
            && iaddr_views(rest@)[i].au == iaddr_views(rest@)[j].au
            implies i == j by {
            assert(rest@[i].au == aus@[i + 1]);
            assert(rest@[j].au == aus@[j + 1]);
            assert(aus@[i + 1] == aus@[j + 1]);
        }
        assert(crate::disk::GenericDisk_v::
            seq_addrs_disjoint_aus(iaddr_views(rest@)));
        crate::disk::GenericDisk_v::to_aus_domain(
            iaddr_views(rest@).to_set(),
        );
        assert(!crate::allocation_layer::AllocationBranchBetree_v::
            seq_addrs_to_aus(iaddr_views(rest@)).contains(first@.au)) by {
            if crate::allocation_layer::AllocationBranchBetree_v::
                seq_addrs_to_aus(iaddr_views(rest@)).contains(first@.au)
            {
                let i = choose |i: int| 0 <= i < rest@.len()
                    && rest@[i]@.au == first@.au;
                assert(aus@[i + 1] == aus@[0]);
                assert(i + 1 != 0);
                assert(false);
            }
        }
        assert_sets_equal!(
            to_aus(iaddr_views(rest@).to_set()).insert(first@.au),
            iau_vec_set(aus@),
            au => {
                if au == first@.au {
                    assert(iau_vec_set(aus@).contains(au)) by {
                        assert(exists |i: int| 0 <= i < aus@.len()
                            && aus@[i] as nat == au) by {
                            assert(aus@[0] as nat == au);
                        }
                    }
                } else if to_aus(iaddr_views(rest@).to_set()).contains(au) {
                    let addr = crate::disk::GenericDisk_v::to_aus_get_addr(
                        iaddr_views(rest@).to_set(),
                        au,
                    );
                    let i = choose |i: int| 0 <= i < rest@.len()
                        && rest@[i]@ == addr;
                    assert(aus@[i + 1] as nat == au);
                    assert(iau_vec_set(aus@).contains(au));
                }
                if iau_vec_set(aus@).contains(au) && au != first@.au {
                    let i = choose |i: int| 0 <= i < aus@.len()
                        && aus@[i] as nat == au;
                    assert(i != 0);
                    assert(rest@[i - 1].au == aus@[i]);
                    assert(iaddr_views(rest@)[i - 1]
                        == rest@[i - 1]@);
                    assert(exists |j: int|
                        0 <= j < iaddr_views(rest@).len()
                            && iaddr_views(rest@)[j]
                                == rest@[i - 1]@) by {
                        assert(iaddr_views(rest@).len() == rest@.len());
                    }
                    assert(iaddr_views(rest@).to_set()
                        .contains(rest@[i - 1]@));
                    assert(to_aus(iaddr_views(rest@).to_set()).contains(au));
                }
            }
        );
    }
    (first, rest)
}

pub open spec fn cached_betree_root_wf(
    cache: Cache::State,
    root: Address,
) -> bool {
    forall |raw: RawPage| #[trigger] cache.valid_read(root, raw) ==> {
        raw_page_to_betree_node(raw).wf()
    }
}

pub enum BetreeRootExtendResult {
    Extended {
        prepared_cache: Ghost<Cache::State>,
        reads: Ghost<Map<Address, RawPage>>,
        writes: Ghost<Map<Address, RawPage>>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub fn extend_root_buffer_with_cache(
    cache: &mut FracCacheImpl,
    old_root: IAddress,
    new_root: IAddress,
    branch_root: IAddress,
) -> (result: BetreeRootExtendResult)
    requires
        old(cache).wf(),
        old_root@.wf(),
        new_root@.wf(),
        branch_root@.wf(),
        old_root@ != new_root@,
        branch_root@ != new_root@,
        cached_betree_root_wf(old(cache)@, old_root@),
    ensures
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        match result {
            BetreeRootExtendResult::Extended {
                prepared_cache,
                reads,
                writes,
            } => {
                &&& reads@.dom() == set![old_root@]
                &&& writes@.dom() == set![new_root@]
                &&& to_betree_nodes(writes@)
                    == flush_memtable_writes(
                        Some(old_root@),
                        branch_root@,
                        new_root@,
                        to_betree_nodes(reads@),
                    )
                &&& Cache::State::next(
                    old(cache)@,
                    prepared_cache@,
                    Cache::Label::Internal,
                )
                &&& forall |read_addr: Address, data: RawPage|
                    read_addr != new_root@
                    && old(cache)@.valid_read(read_addr, data)
                    ==> prepared_cache@.valid_read(read_addr, data)
                &&& Cache::State::next(
                    prepared_cache@,
                    cache@,
                    Cache::Label::Access {
                        reads: reads@,
                        writes: writes@,
                    },
                )
            },
            BetreeRootExtendResult::NeedCacheLoad { addr, handle } => {
                &&& addr == old_root
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, handle)
                &&& forall |read_addr: Address, data: RawPage|
                    old(cache)@.valid_read(read_addr, data)
                    ==> cache@.valid_read(read_addr, data)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    crate::implementation::FracCacheImpl_v::cache_load_label(
                        &addr,
                    ),
                )
            },
            BetreeRootExtendResult::CacheFull
            | BetreeRootExtendResult::Blocked
            | BetreeRootExtendResult::InvalidPage => {
                cache@ == old(cache)@
            },
        },
{
    let ghost cache0 = *cache;
    let handle = match cache.fetch(&old_root, true) {
        FetchErrorCode::Success { slot_handle } => slot_handle,
        FetchErrorCode::LoadInitiate { slot_handle } => {
            return BetreeRootExtendResult::NeedCacheLoad {
                addr: old_root,
                handle: slot_handle,
            };
        },
        FetchErrorCode::CacheFull => {
            return BetreeRootExtendResult::CacheFull;
        },
        FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
            return BetreeRootExtendResult::Blocked;
        },
    };
    let ghost raw = handle.rec@;
    let ghost fetched_slot = handle.idx;
    let fmt = BetreeNodePageFmt::new();
    let all_slice = Slice::all(&handle.rec);
    let parsed = fmt.try_parse(&all_slice, &handle.rec);
    proof {
        assert(cache0@.valid_read(old_root@, raw));
        if parsed is Some {
            assert(fmt == BetreeNodePageFmt::spec_new());
            assert(all_slice@.i(handle.rec@) == raw);
            assert(fmt.parsable(all_slice@.i(handle.rec@)));
            assert(BetreeNodePageFmt::spec_new().parsable(raw));
            assert(parsed.unwrap().parsedv() == fmt.parse(raw));
            assert(raw_page_to_betree_node(raw) == parsed.unwrap()@);
            assert(parsed.unwrap()@.wf());
        }
    }
    let mut node = match parsed {
        Some(node) => node,
        None => {
            cache.handle_release(&old_root, handle);
            return BetreeRootExtendResult::InvalidPage;
        },
    };
    cache.handle_release(&old_root, handle);
    proof {
        assert(cache@ == cache0@) by {
            assert(cache0@.entries
                == cache@.entries.insert(
                    fetched_slot,
                    crate::implementation::Cache_v::Entry::Filled {
                        addr: old_root@,
                        data: raw,
                    },
                ));
            assert(cache@.entries == cache0@.entries);
            assert(cache@.lookup_map == cache0@.lookup_map);
            assert(cache@.status_map == cache0@.status_map);
        }
    }
    if node.buffers.len() >= fmt.buffers_fmt.max_length
        || node.pivots.len() > fmt.pivots_fmt.max_length
        || node.children.len() > fmt.children_fmt.max_length
        || node.flushed.len() > fmt.flushed_fmt.max_length
        || node.buffers.len() >= u8::MAX as usize
        || node.pivots.len() > u8::MAX as usize
        || node.children.len() > u8::MAX as usize
        || node.flushed.len() > u8::MAX as usize
    {
        return BetreeRootExtendResult::Blocked;
    }
    let ghost old_node = node@;
    node.buffers.push(branch_root);
    proof {
        assert(node.wf());
        assert(node@.buffers.addrs
            == old_node.buffers.addrs + seq![branch_root@]);
        assert(node@ == old_node.extend_buffer_seq(
            crate::betree::LinkedSeq_v::LinkedSeq {
                addrs: seq![branch_root@],
            },
        )) by {


        }
        assert(node@.wf());
        assert(node.buffers@.len() <= fmt.buffers_fmt.max_length);
        assert(node.pivots@.len() <= fmt.pivots_fmt.max_length);
        assert(node.children@.len() <= fmt.children_fmt.max_length);
        assert(node.flushed@.len() <= fmt.flushed_fmt.max_length);
        assert(node.buffers@.len() <= u8::MAX as int);
        assert(node.pivots@.len() <= u8::MAX as int);
        assert(node.children@.len() <= u8::MAX as int);
        assert(node.flushed@.len() <= u8::MAX as int);
        bounded_betree_node_marshallable(&node);
    }
    let page = marshall_betree_node_page(&node);
    let ghost reads = map![old_root@ => raw];
    let ghost writes = map![new_root@ => page@];
    let ghost borrowed_cache;
    let ghost prepared_cache;
    let mut reserved = false;
    let mut write_handle = if cache.contains_addr(&new_root) {
        match cache.fetch(&new_root, false) {
            FetchErrorCode::Success { slot_handle } => {
                proof {
                    borrowed_cache = *cache;
                    prepared_cache = cache0@;
                    FracCacheImpl::valid_write_handle_model_entry(
                        &borrowed_cache,
                        &new_root,
                        slot_handle,
                    );
                }
                slot_handle
            },
            FetchErrorCode::CacheFull => {
                return BetreeRootExtendResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BetreeRootExtendResult::Blocked;
            },
            FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                proof { assert(false); }
                return BetreeRootExtendResult::Blocked;
            },
        }
    } else {
        reserved = true;
        match cache.reserve_for_write_absent(&new_root) {
            ReserveWriteResult::Reserved { slot_handle } => {
                proof {
                    borrowed_cache = *cache;
                    prepared_cache = cache@;
                }
                slot_handle
            },
            ReserveWriteResult::CacheFull => {
                return BetreeRootExtendResult::CacheFull;
            },
        }
    };
    let ghost write_slot = write_handle.idx;
    write_handle.rec = page;
    proof {
        assert(cache.valid_write_handle(&new_root, write_handle));
        assert(cache@.valid_write(new_root@));
    }
    cache.write_release(&new_root, write_handle);
    proof {
        assert(prepared_cache.valid_read(old_root@, raw));
        if reserved {
            Cache::State::access_add_reads(
                prepared_cache,
                cache@,
                reads,
                writes,
            );
        } else {
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(
                cache0@,
                prepared_cache,
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
                reads,
                new_root@,
                write_slot,
                page@,
            );
        }
        assert(to_betree_nodes(reads)[old_root@] == old_node);
        assert(to_betree_nodes(writes)[new_root@] == node@);
        assert(to_betree_nodes(writes)
            == flush_memtable_writes(
                Some(old_root@),
                branch_root@,
                new_root@,
                to_betree_nodes(reads),
            )) by {
            assert_maps_equal!(
                to_betree_nodes(writes),
                flush_memtable_writes(
                    Some(old_root@),
                    branch_root@,
                    new_root@,
                    to_betree_nodes(reads),
                ),
                addr => {}
            );
        }
    }
    BetreeRootExtendResult::Extended {
        prepared_cache: Ghost(prepared_cache),
        reads: Ghost(reads),
        writes: Ghost(writes),
    }
}

} // verus!
