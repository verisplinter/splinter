// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle,
};
use crate::spec::ImplDisk_t::IAddress;

verus! {

pub enum CacheWritePrepareResult {
    Ready,
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
}

pub fn prepare_cache_write_addrs(
    cache: &mut FracCacheImpl,
    addrs: &Vec<IAddress>,
) -> (result: CacheWritePrepareResult)
    requires old(cache).wf(),
    ensures
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        match result {
            CacheWritePrepareResult::Ready => {
                &&& cache@ == old(cache)@
                &&& forall |i: int| 0 <= i < addrs@.len()
                    ==> cache.entry_available_for_fetch(
                        &(#[trigger] addrs@[i]),
                    )
            },
            CacheWritePrepareResult::NeedCacheLoad { addr, handle } => {
                &&& exists |i: int| 0 <= i < addrs@.len()
                    && addr == addrs@[i]
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, handle)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    crate::implementation::FracCacheImpl_v::cache_load_label(
                        &addr,
                    ),
                )
            },
            CacheWritePrepareResult::CacheFull
            | CacheWritePrepareResult::Blocked => {
                cache@ == old(cache)@
            },
        },
{
    let ghost cache0 = *cache;
    let mut index = 0usize;
    while index < addrs.len()
        invariant
            cache.wf(),
            cache@ == cache0@,
            cache.valid_load_handles_preserved(cache0),
            index <= addrs.len(),
            forall |i: int| 0 <= i < index
                ==> cache.entry_available_for_fetch(
                    &(#[trigger] addrs@[i]),
                ),
        decreases addrs.len() - index,
    {
        let addr = addrs[index];
        if cache.available_for_fetch(&addr) {
            index += 1;
            continue;
        }
        let ghost cache_pre = *cache;
        match cache.fetch(&addr, true) {
            FetchErrorCode::Success { slot_handle: _ } => {
                proof {
                    assert(cache_pre.entry_available_for_fetch(&addr));
                    assert(false);
                }
                return CacheWritePrepareResult::Blocked;
            },
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    assert(exists |i: int| 0 <= i < addrs@.len()
                        && addr == addrs@[i]) by {
                        assert(addr == addrs@[index as int]);
                    }
                }
                return CacheWritePrepareResult::NeedCacheLoad {
                    addr,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::CacheFull => {
                return CacheWritePrepareResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return CacheWritePrepareResult::Blocked;
            },
        }
    }
    CacheWritePrepareResult::Ready
}

} // verus!
