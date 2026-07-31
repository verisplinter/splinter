// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Projection adapter from the concrete Cache + AsyncDisk pair to the simpler
// CachingDisk abstraction, parameterized by component-owned AUs.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::disk::GenericDisk_v::AU;
use crate::implementation::Cache_v::{Cache, Entry, Slot, Status as CacheStatus};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, status_map, CachingDisk, PageStatus as CachingDiskPageStatus,
};
use crate::spec::AsyncDisk_t::{Address, AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::MapSpec_t::ID;

verus! {

pub open spec fn cache_filled_addr(cache: Cache::State, addr: Address) -> bool
{
    &&& cache.lookup_map.contains_key(addr)
    &&& cache.entries.contains_key(cache.lookup_map[addr])
    &&& cache.entries[cache.lookup_map[addr]] is Filled
}

pub open spec fn cache_filled_page(cache: Cache::State, addr: Address) -> RawPage
    recommends cache_filled_addr(cache, addr)
{
    cache.entries[cache.lookup_map[addr]]->data
}

pub open spec fn filled_cache_pages(cache: Cache::State) -> Map<Address, RawPage>
{
    Map::new(
        |addr: Address| cache_filled_addr(cache, addr),
        |addr: Address| cache_filled_page(cache, addr),
    )
}

pub open spec fn cache_status_i(cache: Cache::State, addr: Address) -> CachingDiskPageStatus
    recommends
        cache_filled_addr(cache, addr),
        cache.status_map.contains_key(cache.lookup_map[addr]),
{
    if cache.status_map[cache.lookup_map[addr]] == CacheStatus::Dirty {
        CachingDiskPageStatus::Dirty
    } else if cache.status_map[cache.lookup_map[addr]] == CacheStatus::Writeback {
        CachingDiskPageStatus::Writeback
    } else {
        CachingDiskPageStatus::Clean
    }
}

pub open spec fn filled_cache_status(cache: Cache::State) -> Map<Address, CachingDiskPageStatus>
{
    Map::new(
        |addr: Address| {
            &&& cache_filled_addr(cache, addr)
            &&& cache.status_map.contains_key(cache.lookup_map[addr])
        },
        |addr: Address| cache_status_i(cache, addr),
    )
}

// Raw cache projections expose every filled cache entry in the selected range.
pub open spec fn project_cache_pages(
    cache: Cache::State,
    owned_aus: Set<AU>,
) -> Map<Address, RawPage>
{
    filled_cache_pages(cache).restrict(addresses_in_aus(owned_aus))
}

pub open spec fn project_cache_pages_by_addrs(
    cache: Cache::State,
    addrs: Set<Address>,
) -> Map<Address, RawPage>
{
    filled_cache_pages(cache).restrict(addrs)
}

pub open spec fn project_cache_status(
    cache: Cache::State,
    owned_aus: Set<AU>,
) -> Map<Address, CachingDiskPageStatus>
{
    filled_cache_status(cache).restrict(addresses_in_aus(owned_aus))
}

pub open spec fn project_cache_status_by_addrs(
    cache: Cache::State,
    addrs: Set<Address>,
) -> Map<Address, CachingDiskPageStatus>
{
    filled_cache_status(cache).restrict(addrs)
}

pub open spec fn project_persistent(
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
) -> Map<Address, RawPage>
{
    disk.content.restrict(addresses_in_aus(owned_aus))
}

pub open spec fn project_persistent_by_addrs(
    disk: AsyncDisk::State,
    addrs: Set<Address>,
) -> Map<Address, RawPage>
{
    disk.content.restrict(addrs)
}

pub open spec fn caching_disk_i(
    cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
) -> CachingDisk::State
{
    let persistent = project_persistent(disk, owned_aus);
    CachingDisk::State{
        cache: project_cache_pages(cache, owned_aus),
        persistent,
        status: project_cache_status(cache, owned_aus),
    }
}

pub open spec fn caching_disk_i_by_domains(
    cache: Cache::State,
    disk: AsyncDisk::State,
    cache_addrs: Set<Address>,
    persistent_addrs: Set<Address>,
) -> CachingDisk::State
{
    let persistent = project_persistent_by_addrs(disk, persistent_addrs);
    CachingDisk::State{
        cache: project_cache_pages_by_addrs(cache, cache_addrs),
        persistent,
        status: project_cache_status_by_addrs(cache, cache_addrs),
    }
}

pub open spec fn disk_has_pending_id(disk: AsyncDisk::State, id: ID) -> bool
{
    ||| disk.requests.contains_key(id)
    ||| disk.responses.contains_key(id)
}

pub open spec fn outstanding_cache_io_wf(
    cache: Cache::State,
    disk: AsyncDisk::State,
    outstanding: Map<ID, Address>,
) -> bool
{
    &&& outstanding.is_injective()
    &&& forall |id: ID| #[trigger] outstanding.contains_key(id)
        ==> disk_has_pending_id(disk, id)
    &&& forall |id: ID| #[trigger] outstanding.contains_key(id)
        && disk.requests.contains_key(id) ==> {
            let addr = outstanding[id];
            let req = disk.requests[id];
            &&& req.addr() == addr
            &&& req is WriteReq ==> {
                &&& cache.lookup_map.contains_key(addr)
                &&& cache.entries[cache.lookup_map[addr]] is Filled
                &&& cache.entries[cache.lookup_map[addr]]->data == req->data
                &&& cache.status_map[cache.lookup_map[addr]] == CacheStatus::Writeback
            }
        }
}

pub proof fn caching_disk_i_by_domains_inv_from_clean_cache_coupling(
    cache: Cache::State,
    disk: AsyncDisk::State,
    cache_addrs: Set<Address>,
    persistent_addrs: Set<Address>,
)
    requires
        cache.inv(),
        forall |addr: Address| #[trigger] filled_cache_status(cache).contains_key(addr)
            && filled_cache_status(cache)[addr] == CachingDiskPageStatus::Clean
            && cache_addrs.contains(addr)
            && project_persistent_by_addrs(disk, persistent_addrs).contains_key(addr)
            ==> {
                &&& disk.content[addr] == cache_filled_page(cache, addr)
            },
    ensures
        caching_disk_i_by_domains(cache, disk, cache_addrs, persistent_addrs).inv(),
{
    let cd = caching_disk_i_by_domains(cache, disk, cache_addrs, persistent_addrs);
    assert(cd.status.dom() =~= cd.cache.dom()) by {
        assert forall |addr: Address| #[trigger] cd.status.dom().contains(addr)
            implies cd.cache.dom().contains(addr) by {
            assert(cache_addrs.contains(addr));
            assert(filled_cache_status(cache).contains_key(addr));
            assert(cache_filled_addr(cache, addr));
            assert(filled_cache_pages(cache).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache, cache_addrs).contains_key(addr));
        }
        assert forall |addr: Address| #[trigger] cd.cache.dom().contains(addr)
            implies cd.status.dom().contains(addr) by {
            assert(cache_addrs.contains(addr));
            assert(filled_cache_pages(cache).contains_key(addr));
            assert(cache_filled_addr(cache, addr));
            assert(filled_cache_status(cache).contains_key(addr));
            assert(project_cache_status_by_addrs(cache, cache_addrs).contains_key(addr));
        }
    }
    assert forall |addr: Address| #[trigger] cd.status.contains_key(addr)
        && cd.status[addr] == CachingDiskPageStatus::Clean
        implies {
            cd.persistent.contains_key(addr) ==> cd.persistent[addr] == cd.cache[addr]
        } by {
        assert(cache_addrs.contains(addr));
        assert(filled_cache_status(cache).contains_key(addr));
        assert(filled_cache_status(cache)[addr] == CachingDiskPageStatus::Clean);
        if cd.persistent.contains_key(addr) {
            assert(project_persistent_by_addrs(disk, persistent_addrs).contains_key(addr));
            assert(disk.content[addr] == cache_filled_page(cache, addr));
            assert(cd.persistent[addr] == disk.content[addr]);
            assert(cd.cache[addr] == cache_filled_page(cache, addr));
        }
    }
    cd.clean_pages_agree_from_forall();
}

pub proof fn caching_disk_i_inv_from_clean_cache_coupling(
    cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
)
    requires
        cache.inv(),
        forall |addr: Address| #[trigger] filled_cache_status(cache).contains_key(addr)
            && filled_cache_status(cache)[addr] == CachingDiskPageStatus::Clean
            && addresses_in_aus(owned_aus).contains(addr)
            && project_persistent(disk, owned_aus).contains_key(addr)
            ==> {
                &&& disk.content[addr] == cache_filled_page(cache, addr)
            },
    ensures
        caching_disk_i(cache, disk, owned_aus).inv(),
{
    caching_disk_i_by_domains_inv_from_clean_cache_coupling(
        cache,
        disk,
        addresses_in_aus(owned_aus),
        addresses_in_aus(owned_aus),
    );
}

pub proof fn caching_disk_i_domains_wf_from_sources(
    cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
)
    requires
        forall |addr: Address| #[trigger] filled_cache_pages(cache).contains_key(addr)
            ==> addr.wf(),
        forall |addr: Address| {
            &&& #[trigger] disk.content.contains_key(addr)
            &&& addresses_in_aus(owned_aus).contains(addr)
        } ==> addr.wf(),
    ensures
        caching_disk_i(cache, disk, owned_aus).cache.dom()
            <= Set::new(|addr: Address| addr.wf()),
        caching_disk_i(cache, disk, owned_aus).persistent.dom()
            <= Set::new(|addr: Address| addr.wf()),
{
    let cd = caching_disk_i(cache, disk, owned_aus);
    assert forall |addr: Address| #[trigger] cd.cache.dom().contains(addr)
        implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
        assert(project_cache_pages(cache, owned_aus).contains_key(addr));
        assert(filled_cache_pages(cache).contains_key(addr));
        assert(addr.wf());
    }
    assert forall |addr: Address| #[trigger] cd.persistent.dom().contains(addr)
        implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
        assert(project_persistent(disk, owned_aus).contains_key(addr));
        assert(disk.content.contains_key(addr));
        assert(addr.wf());
    }
}

pub proof fn caching_disk_i_by_domains_equal_from_raw_projection_agreement(
    cache1: Cache::State,
    cache2: Cache::State,
    disk1: AsyncDisk::State,
    disk2: AsyncDisk::State,
    cache_addrs: Set<Address>,
    persistent_addrs: Set<Address>,
)
    requires
        project_cache_pages_by_addrs(cache1, cache_addrs)
            == project_cache_pages_by_addrs(cache2, cache_addrs),
        project_cache_status_by_addrs(cache1, cache_addrs)
            == project_cache_status_by_addrs(cache2, cache_addrs),
        project_persistent_by_addrs(disk1, persistent_addrs)
            == project_persistent_by_addrs(disk2, persistent_addrs),
    ensures
        caching_disk_i_by_domains(cache1, disk1, cache_addrs, persistent_addrs)
            == caching_disk_i_by_domains(cache2, disk2, cache_addrs, persistent_addrs),
{
    let cd1 = caching_disk_i_by_domains(cache1, disk1, cache_addrs, persistent_addrs);
    let cd2 = caching_disk_i_by_domains(cache2, disk2, cache_addrs, persistent_addrs);
    assert(cd1.persistent == cd2.persistent);
    assert_maps_equal!(cd1.cache, cd2.cache, addr => {
        if cd1.cache.contains_key(addr) {
            assert(project_cache_pages_by_addrs(cache1, cache_addrs).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache1, cache_addrs).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache2, cache_addrs).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache1, cache_addrs)[addr]
                == project_cache_pages_by_addrs(cache2, cache_addrs)[addr]);
            assert(project_cache_pages_by_addrs(cache1, cache_addrs)[addr]
                == cache_filled_page(cache1, addr));
            assert(project_cache_pages_by_addrs(cache2, cache_addrs)[addr]
                == cache_filled_page(cache2, addr));
            assert(cd2.cache.contains_key(addr));
            assert(cd1.cache[addr] == cd2.cache[addr]);
        }
        if cd2.cache.contains_key(addr) {
            assert(project_cache_pages_by_addrs(cache2, cache_addrs).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache2, cache_addrs).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache1, cache_addrs).contains_key(addr));
            assert(project_cache_pages_by_addrs(cache2, cache_addrs)[addr]
                == project_cache_pages_by_addrs(cache1, cache_addrs)[addr]);
            assert(project_cache_pages_by_addrs(cache2, cache_addrs)[addr]
                == cache_filled_page(cache2, addr));
            assert(project_cache_pages_by_addrs(cache1, cache_addrs)[addr]
                == cache_filled_page(cache1, addr));
            assert(cd1.cache.contains_key(addr));
            assert(cd1.cache[addr] == cd2.cache[addr]);
        }
    });
    assert_maps_equal!(cd1.status, cd2.status, addr => {
        if cd1.status.contains_key(addr) {
            assert(project_cache_status_by_addrs(cache1, cache_addrs).contains_key(addr));
            assert(project_cache_status_by_addrs(cache1, cache_addrs).contains_key(addr));
            assert(project_cache_status_by_addrs(cache2, cache_addrs).contains_key(addr));
            assert(project_cache_status_by_addrs(cache1, cache_addrs)[addr]
                == project_cache_status_by_addrs(cache2, cache_addrs)[addr]);
            assert(project_cache_status_by_addrs(cache1, cache_addrs)[addr]
                == filled_cache_status(cache1)[addr]);
            assert(project_cache_status_by_addrs(cache2, cache_addrs)[addr]
                == filled_cache_status(cache2)[addr]);
            assert(filled_cache_status(cache1)[addr] == filled_cache_status(cache2)[addr]);
            assert(cd2.status.contains_key(addr));
            assert(cd1.status[addr] == cd2.status[addr]);
        }
        if cd2.status.contains_key(addr) {
            assert(project_cache_status_by_addrs(cache2, cache_addrs).contains_key(addr));
            assert(project_cache_status_by_addrs(cache2, cache_addrs).contains_key(addr));
            assert(project_cache_status_by_addrs(cache1, cache_addrs).contains_key(addr));
            assert(project_cache_status_by_addrs(cache2, cache_addrs)[addr]
                == project_cache_status_by_addrs(cache1, cache_addrs)[addr]);
            assert(project_cache_status_by_addrs(cache2, cache_addrs)[addr]
                == filled_cache_status(cache2)[addr]);
            assert(project_cache_status_by_addrs(cache1, cache_addrs)[addr]
                == filled_cache_status(cache1)[addr]);
            assert(filled_cache_status(cache2)[addr] == filled_cache_status(cache1)[addr]);
            assert(cd1.status.contains_key(addr));
            assert(cd1.status[addr] == cd2.status[addr]);
        }
    });
}

pub proof fn caching_disk_i_equal_from_raw_projection_agreement(
    cache1: Cache::State,
    cache2: Cache::State,
    disk1: AsyncDisk::State,
    disk2: AsyncDisk::State,
    owned_aus: Set<AU>,
)
    requires
        project_cache_pages(cache1, owned_aus) == project_cache_pages(cache2, owned_aus),
        project_cache_status(cache1, owned_aus) == project_cache_status(cache2, owned_aus),
        project_persistent(disk1, owned_aus) == project_persistent(disk2, owned_aus),
    ensures
        caching_disk_i(cache1, disk1, owned_aus) == caching_disk_i(cache2, disk2, owned_aus),
{
    caching_disk_i_by_domains_equal_from_raw_projection_agreement(
        cache1,
        cache2,
        disk1,
        disk2,
        addresses_in_aus(owned_aus),
        addresses_in_aus(owned_aus),
    );
}

pub proof fn caching_disk_i_equal_by_aus_ext(
    cache: Cache::State,
    disk: AsyncDisk::State,
    aus1: Set<AU>,
    aus2: Set<AU>,
)
    requires
        aus1 =~= aus2,
    ensures
        caching_disk_i(cache, disk, aus1) == caching_disk_i(cache, disk, aus2),
{
    let cd1 = caching_disk_i(cache, disk, aus1);
    let cd2 = caching_disk_i(cache, disk, aus2);
    assert(addresses_in_aus(aus1) =~= addresses_in_aus(aus2));
    assert(cd1.persistent == cd2.persistent) by {
        assert_maps_equal!(cd1.persistent, cd2.persistent, addr => {
            assert(addresses_in_aus(aus1).contains(addr)
                <==> addresses_in_aus(aus2).contains(addr));
        });
    }
    assert_maps_equal!(cd1.cache, cd2.cache, addr => {
        assert(addresses_in_aus(aus1).contains(addr)
            <==> addresses_in_aus(aus2).contains(addr));
        if cd1.cache.contains_key(addr) {
            assert(project_cache_pages(cache, aus1).contains_key(addr));
            assert(cd2.cache.contains_key(addr));
            assert(cd1.cache[addr] == cd2.cache[addr]);
        }
        if cd2.cache.contains_key(addr) {
            assert(project_cache_pages(cache, aus2).contains_key(addr));
            assert(cd1.cache.contains_key(addr));
            assert(cd1.cache[addr] == cd2.cache[addr]);
        }
    });
    assert_maps_equal!(cd1.status, cd2.status, addr => {
        assert(addresses_in_aus(aus1).contains(addr)
            <==> addresses_in_aus(aus2).contains(addr));
        if cd1.status.contains_key(addr) {
            assert(project_cache_status(cache, aus1).contains_key(addr));
            assert(cd2.status.contains_key(addr));
            assert(cd1.status[addr] == cd2.status[addr]);
        }
        if cd2.status.contains_key(addr) {
            assert(project_cache_status(cache, aus2).contains_key(addr));
            assert(cd1.status.contains_key(addr));
            assert(cd1.status[addr] == cd2.status[addr]);
        }
    });
}

pub proof fn projectable_entry_in_caching_disk_i(
    cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    addr: Address,
)
    requires
        project_cache_pages(cache, owned_aus).contains_key(addr),
    ensures
        caching_disk_i(cache, disk, owned_aus).cache.contains_key(addr),
        caching_disk_i(cache, disk, owned_aus).cache[addr] == project_cache_pages(cache, owned_aus)[addr],
{
    let cd = caching_disk_i(cache, disk, owned_aus);
    assert(addresses_in_aus(owned_aus).contains(addr));
    assert(filled_cache_pages(cache).contains_key(addr));
    assert(project_cache_pages(cache, owned_aus).contains_key(addr));
    assert(cd.cache[addr] == cache_filled_page(cache, addr));
    assert(project_cache_pages(cache, owned_aus)[addr] == cache_filled_page(cache, addr));
}

pub proof fn valid_reads_in_project_cache_by_addrs(
    cache: Cache::State,
    addrs: Set<Address>,
    reads: Map<Address, RawPage>,
)
    requires
        cache.inv(),
        reads.dom() <= addrs,
        forall |addr: Address| #[trigger] reads.contains_key(addr)
            ==> cache.valid_read(addr, reads[addr]),
    ensures
        reads <= project_cache_pages_by_addrs(cache, addrs),
{
    cache.build_lookup_map_ensures();
    assert(cache.build_lookup_map_props(cache.lookup_map));
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies {
            &&& project_cache_pages_by_addrs(cache, addrs).contains_key(addr)
            &&& project_cache_pages_by_addrs(cache, addrs)[addr] == reads[addr]
        } by {
        assert(addrs.contains(addr));
        assert(cache.valid_read(addr, reads[addr]));
        let slot = cache.lookup_map[addr];
        assert(cache.entries.contains_key(slot));
        assert(cache.entries[slot] is Filled);
        assert(cache.entries[slot].get_addr() == addr);
        assert(cache_filled_addr(cache, addr));
        assert(filled_cache_pages(cache).contains_key(addr));
        assert(cache_filled_page(cache, addr) == reads[addr]);
        assert(project_cache_pages_by_addrs(cache, addrs).contains_key(addr));
        assert(project_cache_pages_by_addrs(cache, addrs)[addr] == reads[addr]);
    }
}

pub proof fn cache_access_reads_in_project_cache_by_addrs(
    pre: Cache::State,
    post: Cache::State,
    addrs: Set<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Access{reads, writes}),
        reads.dom() <= addrs,
    ensures
        reads <= project_cache_pages_by_addrs(pre, addrs),
{
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies pre.valid_read(addr, reads[addr]) by {
        Cache::State::access_read_valid(pre, post, reads, writes, addr);
    }
    valid_reads_in_project_cache_by_addrs(pre, addrs, reads);
}

pub proof fn cache_access_reads_in_caching_disk_i_by_domains(
    pre: Cache::State,
    post: Cache::State,
    disk: AsyncDisk::State,
    cache_addrs: Set<Address>,
    persistent_addrs: Set<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Access{reads, writes}),
        reads.dom() <= cache_addrs,
    ensures
        reads <= caching_disk_i_by_domains(pre, disk, cache_addrs, persistent_addrs).cache,
{
    cache_access_reads_in_project_cache_by_addrs(pre, post, cache_addrs, reads, writes);
}

pub proof fn backed_raw_cache_entry_in_caching_disk_i_visible(
    cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    addr: Address,
)
    requires
        project_cache_pages(cache, owned_aus).contains_key(addr),
        project_persistent(disk, owned_aus).contains_key(addr),
        project_persistent(disk, owned_aus)[addr] == project_cache_pages(cache, owned_aus)[addr],
    ensures
        caching_disk_i(cache, disk, owned_aus).visible().contains_key(addr),
        caching_disk_i(cache, disk, owned_aus).visible()[addr] == project_cache_pages(cache, owned_aus)[addr],
{
    let cd = caching_disk_i(cache, disk, owned_aus);
    assert(cd.cache.contains_key(addr));
    assert(cd.cache[addr] == project_cache_pages(cache, owned_aus)[addr]);
    assert(cd.persistent.contains_key(addr));
    assert(cd.persistent[addr] == project_cache_pages(cache, owned_aus)[addr]);
    if cd.visible_cache().contains_key(addr) {
        assert(cd.visible_cache()[addr] == cd.cache[addr]);
        assert(cd.visible()[addr] == cd.cache[addr]);
    } else {
        assert(cd.visible()[addr] == cd.persistent[addr]);
    }
}

pub proof fn projected_cache_access_effect(
    pre: Cache::State,
    post: Cache::State,
    owned_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Access{reads, writes}),
        writes.dom() <= addresses_in_aus(owned_aus),
    ensures
        project_cache_pages(post, owned_aus)
            =~= project_cache_pages(pre, owned_aus).union_prefer_right(writes),
        project_cache_status(post, owned_aus)
            =~= project_cache_status(pre, owned_aus)
                .union_prefer_right(status_map(writes.dom(), CachingDiskPageStatus::Dirty)),
{
    let lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre, post, lbl);
    pre.build_lookup_map_ensures();
    post.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(pre, post, lbl, Cache::Step::access()));
    reveal(Cache::State::access);
    let updated_entries = pre.write_updated_entries(writes);
    let updated_status = pre.write_updated_status(writes);
    assert(post.lookup_map == pre.lookup_map);
    assert(post.entries == pre.entries.union_prefer_right(updated_entries));
    assert(post.status_map == pre.status_map.union_prefer_right(updated_status));

    assert_maps_equal!(
        project_cache_pages(post, owned_aus),
        project_cache_pages(pre, owned_aus).union_prefer_right(writes),
        addr => {
            if writes.contains_key(addr) {
                assert(addresses_in_aus(owned_aus).contains(addr));
                assert(pre.valid_write(addr));
                assert(pre.lookup_map.contains_key(addr));
                let slot = pre.lookup_map[addr];
                if pre.entries[slot] is Filled {
                    assert(pre.entries[slot].get_addr() == addr);
                } else {
                    assert(pre.entries[slot] is Reserved);
                    assert(pre.entries[slot].get_addr() == addr);
                }
                let restricted = pre.lookup_map.restrict(writes.dom());
                assert(restricted.contains_key(addr));
                assert(restricted[addr] == slot);
                assert(restricted.values().contains(slot));
                assert(updated_entries.contains_key(slot));
                assert(post.entries[slot] == Entry::Filled{addr, data: writes[addr]});
                assert(cache_filled_addr(post, addr));
                assert(project_cache_pages(post, owned_aus).contains_key(addr));
                assert(project_cache_pages(post, owned_aus)[addr] == writes[addr]);
            } else {
                Cache::State::access_unwritten_addr_unchanged(pre, post, reads, writes, addr);
                if project_cache_pages(post, owned_aus).contains_key(addr) {
                    assert(addresses_in_aus(owned_aus).contains(addr));
                    assert(cache_filled_addr(post, addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]]);
                }
                if project_cache_pages(pre, owned_aus).contains_key(addr) {
                    assert(addresses_in_aus(owned_aus).contains(addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(cache_filled_addr(post, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]]);
                }
            }
        }
    );
    assert_maps_equal!(
        project_cache_status(post, owned_aus),
        project_cache_status(pre, owned_aus)
            .union_prefer_right(status_map(writes.dom(), CachingDiskPageStatus::Dirty)),
        addr => {
            if writes.contains_key(addr) {
                assert(addresses_in_aus(owned_aus).contains(addr));
                assert(pre.valid_write(addr));
                assert(pre.lookup_map.contains_key(addr));
                let slot = pre.lookup_map[addr];
                let restricted = pre.lookup_map.restrict(writes.dom());
                assert(restricted.contains_key(addr));
                assert(restricted[addr] == slot);
                assert(restricted.values().contains(slot));
                assert(updated_status.contains_key(slot));
                assert(post.status_map[slot] == CacheStatus::Dirty);
                assert(cache_filled_addr(post, addr));
                assert(project_cache_status(post, owned_aus)[addr] == CachingDiskPageStatus::Dirty);
            } else {
                Cache::State::access_unwritten_addr_unchanged(pre, post, reads, writes, addr);
                if project_cache_status(post, owned_aus).contains_key(addr) {
                    assert(addresses_in_aus(owned_aus).contains(addr));
                    assert(cache_filled_addr(post, addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.status_map[post.lookup_map[addr]]
                        == pre.status_map[pre.lookup_map[addr]]);
                }
                if project_cache_status(pre, owned_aus).contains_key(addr) {
                    assert(addresses_in_aus(owned_aus).contains(addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(cache_filled_addr(post, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.status_map[post.lookup_map[addr]]
                        == pre.status_map[pre.lookup_map[addr]]);
                }
            }
        }
    );
}

pub proof fn projected_cache_access_effect_by_addrs(
    pre: Cache::State,
    post: Cache::State,
    addrs: Set<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Access{reads, writes}),
        writes.dom() <= addrs,
    ensures
        project_cache_pages_by_addrs(post, addrs)
            =~= project_cache_pages_by_addrs(pre, addrs).union_prefer_right(writes),
        project_cache_status_by_addrs(post, addrs)
            =~= project_cache_status_by_addrs(pre, addrs)
                .union_prefer_right(status_map(writes.dom(), CachingDiskPageStatus::Dirty)),
{
    let lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre, post, lbl);
    pre.build_lookup_map_ensures();
    post.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(pre, post, lbl, Cache::Step::access()));
    let updated_entries = pre.write_updated_entries(writes);
    let updated_status = pre.write_updated_status(writes);
    assert(post.lookup_map == pre.lookup_map);
    assert(post.entries == pre.entries.union_prefer_right(updated_entries));
    assert(post.status_map == pre.status_map.union_prefer_right(updated_status));

    assert_maps_equal!(
        project_cache_pages_by_addrs(post, addrs),
        project_cache_pages_by_addrs(pre, addrs).union_prefer_right(writes),
        addr => {
            if writes.contains_key(addr) {
                assert(addrs.contains(addr));
                assert(pre.valid_write(addr));
                assert(pre.lookup_map.contains_key(addr));
                let slot = pre.lookup_map[addr];
                if pre.entries[slot] is Filled {
                    assert(pre.entries[slot].get_addr() == addr);
                } else {
                    assert(pre.entries[slot] is Reserved);
                    assert(pre.entries[slot].get_addr() == addr);
                }
                let restricted = pre.lookup_map.restrict(writes.dom());
                assert(restricted.contains_key(addr));
                assert(restricted[addr] == slot);
                assert(restricted.values().contains(slot));
                assert(updated_entries.contains_key(slot));
                assert(post.entries[slot] == Entry::Filled{addr, data: writes[addr]});
                assert(cache_filled_addr(post, addr));
                assert(project_cache_pages_by_addrs(post, addrs).contains_key(addr));
                assert(project_cache_pages_by_addrs(post, addrs)[addr] == writes[addr]);
            } else {
                Cache::State::access_unwritten_addr_unchanged(pre, post, reads, writes, addr);
                if project_cache_pages_by_addrs(post, addrs).contains_key(addr) {
                    assert(addrs.contains(addr));
                    assert(cache_filled_addr(post, addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]]);
                }
                if project_cache_pages_by_addrs(pre, addrs).contains_key(addr) {
                    assert(addrs.contains(addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(cache_filled_addr(post, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]]);
                }
            }
        }
    );
    assert_maps_equal!(
        project_cache_status_by_addrs(post, addrs),
        project_cache_status_by_addrs(pre, addrs)
            .union_prefer_right(status_map(writes.dom(), CachingDiskPageStatus::Dirty)),
        addr => {
            if writes.contains_key(addr) {
                assert(addrs.contains(addr));
                assert(pre.valid_write(addr));
                assert(pre.lookup_map.contains_key(addr));
                let slot = pre.lookup_map[addr];
                let restricted = pre.lookup_map.restrict(writes.dom());
                assert(restricted.contains_key(addr));
                assert(restricted[addr] == slot);
                assert(restricted.values().contains(slot));
                assert(updated_status.contains_key(slot));
                assert(post.status_map[slot] == CacheStatus::Dirty);
                assert(cache_filled_addr(post, addr));
                assert(project_cache_status_by_addrs(post, addrs)[addr] == CachingDiskPageStatus::Dirty);
            } else {
                Cache::State::access_unwritten_addr_unchanged(pre, post, reads, writes, addr);
                if project_cache_status_by_addrs(post, addrs).contains_key(addr) {
                    assert(addrs.contains(addr));
                    assert(cache_filled_addr(post, addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.status_map[post.lookup_map[addr]]
                        == pre.status_map[pre.lookup_map[addr]]);
                }
                if project_cache_status_by_addrs(pre, addrs).contains_key(addr) {
                    assert(addrs.contains(addr));
                    assert(cache_filled_addr(pre, addr));
                    assert(cache_filled_addr(post, addr));
                    assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                    assert(post.status_map[post.lookup_map[addr]]
                        == pre.status_map[pre.lookup_map[addr]]);
                }
            }
        }
    );
}

pub proof fn cache_access_refines_caching_disk_access(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Access{reads, writes}),
        reads.dom() <= addresses_in_aus(owned_aus),
        writes.dom() <= addresses_in_aus(owned_aus),
    ensures
        CachingDisk::State::next(
            caching_disk_i(pre_cache, disk, owned_aus),
            caching_disk_i(post_cache, disk, owned_aus),
            CachingDisk::Label::Access{reads, writes},
        ),
{
    cache_access_refines_caching_disk_access_by_domains(
        pre_cache,
        post_cache,
        disk,
        addresses_in_aus(owned_aus),
        addresses_in_aus(owned_aus),
        reads,
        writes,
    );
}

pub proof fn cache_access_refines_caching_disk_access_by_domains(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    cache_addrs: Set<Address>,
    persistent_addrs: Set<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Access{reads, writes}),
        reads.dom() <= cache_addrs,
        writes.dom() <= cache_addrs,
    ensures
        CachingDisk::State::next(
            caching_disk_i_by_domains(pre_cache, disk, cache_addrs, persistent_addrs),
            caching_disk_i_by_domains(post_cache, disk, cache_addrs, persistent_addrs),
            CachingDisk::Label::Access{reads, writes},
        ),
{
    let pre_cd = caching_disk_i_by_domains(pre_cache, disk, cache_addrs, persistent_addrs);
    let post_cd = caching_disk_i_by_domains(post_cache, disk, cache_addrs, persistent_addrs);
    let lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    projected_cache_access_effect_by_addrs(pre_cache, post_cache, cache_addrs, reads, writes);
    assert(pre_cd.persistent == post_cd.persistent);
    assert_maps_equal!(
        post_cd.cache,
        pre_cd.cache.union_prefer_right(writes),
        addr => {
            if writes.contains_key(addr) {
                assert(cache_addrs.contains(addr));
                assert(project_cache_pages_by_addrs(post_cache, cache_addrs).contains_key(addr));
                assert(project_cache_pages_by_addrs(post_cache, cache_addrs)[addr] == writes[addr]);
                assert(project_cache_status_by_addrs(post_cache, cache_addrs).contains_key(addr));
                assert(project_cache_status_by_addrs(post_cache, cache_addrs)[addr]
                    == CachingDiskPageStatus::Dirty);
                assert(filled_cache_status(post_cache).contains_key(addr));
                assert(post_cd.cache[addr] == writes[addr]);
            } else {
                if post_cd.cache.contains_key(addr) {
                    assert(project_cache_pages_by_addrs(post_cache, cache_addrs).contains_key(addr));
                    assert(cache_addrs.contains(addr));
                    assert(filled_cache_pages(post_cache).contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    Cache::State::access_unwritten_addr_unchanged(
                        pre_cache,
                        post_cache,
                        reads,
                        writes,
                        addr,
                    );
                    assert(filled_cache_pages(pre_cache).contains_key(addr));
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                    assert(post_cache.entries[post_cache.lookup_map[addr]]
                        == pre_cache.entries[pre_cache.lookup_map[addr]]);
                    assert(filled_cache_status(post_cache).contains_key(addr));
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(filled_cache_status(post_cache)[addr]
                        == filled_cache_status(pre_cache)[addr]);
                    assert(pre_cd.cache.contains_key(addr));
                    assert(pre_cd.cache[addr] == post_cd.cache[addr]);
                }
                if pre_cd.cache.contains_key(addr) {
                    assert(project_cache_pages_by_addrs(pre_cache, cache_addrs).contains_key(addr));
                    assert(cache_addrs.contains(addr));
                    assert(filled_cache_pages(pre_cache).contains_key(addr));
                    assert(cache_filled_addr(pre_cache, addr));
                    Cache::State::access_unwritten_addr_unchanged(
                        pre_cache,
                        post_cache,
                        reads,
                        writes,
                        addr,
                    );
                    assert(filled_cache_pages(post_cache).contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                    assert(post_cache.entries[post_cache.lookup_map[addr]]
                        == pre_cache.entries[pre_cache.lookup_map[addr]]);
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(filled_cache_status(post_cache).contains_key(addr));
                    assert(filled_cache_status(post_cache)[addr]
                        == filled_cache_status(pre_cache)[addr]);
                    assert(post_cd.cache.contains_key(addr));
                    assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                }
            }
        }
    );
    assert_maps_equal!(
        post_cd.status,
        pre_cd.status.union_prefer_right(status_map(writes.dom(), CachingDiskPageStatus::Dirty)),
        addr => {
            if writes.contains_key(addr) {
                assert(cache_addrs.contains(addr));
                assert(project_cache_status_by_addrs(post_cache, cache_addrs).contains_key(addr));
                assert(project_cache_status_by_addrs(post_cache, cache_addrs)[addr]
                    == CachingDiskPageStatus::Dirty);
                assert(filled_cache_status(post_cache).contains_key(addr));
                assert(post_cd.status[addr] == CachingDiskPageStatus::Dirty);
            } else {
                if post_cd.status.contains_key(addr) {
                    assert(project_cache_status_by_addrs(post_cache, cache_addrs).contains_key(addr));
                    assert(cache_addrs.contains(addr));
                    assert(filled_cache_status(post_cache).contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    Cache::State::access_unwritten_addr_unchanged(
                        pre_cache,
                        post_cache,
                        reads,
                        writes,
                        addr,
                    );
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                    assert(post_cache.status_map[post_cache.lookup_map[addr]]
                        == pre_cache.status_map[pre_cache.lookup_map[addr]]);
                    assert(filled_cache_status(post_cache).contains_key(addr));
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(filled_cache_status(post_cache)[addr]
                        == filled_cache_status(pre_cache)[addr]);
                    assert(pre_cd.status.contains_key(addr));
                    assert(pre_cd.status[addr] == post_cd.status[addr]);
                }
                if pre_cd.status.contains_key(addr) {
                    assert(project_cache_status_by_addrs(pre_cache, cache_addrs).contains_key(addr));
                    assert(cache_addrs.contains(addr));
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(cache_filled_addr(pre_cache, addr));
                    Cache::State::access_unwritten_addr_unchanged(
                        pre_cache,
                        post_cache,
                        reads,
                        writes,
                        addr,
                    );
                    assert(filled_cache_status(post_cache).contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                    assert(post_cache.status_map[post_cache.lookup_map[addr]]
                        == pre_cache.status_map[pre_cache.lookup_map[addr]]);
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(filled_cache_status(post_cache).contains_key(addr));
                    assert(filled_cache_status(post_cache)[addr]
                        == filled_cache_status(pre_cache)[addr]);
                    assert(post_cd.status.contains_key(addr));
                    assert(post_cd.status[addr] == pre_cd.status[addr]);
                }
            }
        }
    );
    assert forall |addr: Address| #[trigger] writes.contains_key(addr)
        && pre_cd.status.contains_key(addr)
        implies !(pre_cd.status[addr] == CachingDiskPageStatus::Writeback) by {
        assert(pre_cache.valid_write(addr)) by {
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(
                pre_cache,
                post_cache,
                Cache::Label::Access{reads, writes},
                Cache::Step::access(),
            ));
        }
        assert(pre_cache.lookup_map.contains_key(addr));
        let slot = pre_cache.lookup_map[addr];
        assert(cache_filled_addr(pre_cache, addr));
        if pre_cache.status_map[slot] == CacheStatus::Writeback {
            assert(pre_cd.status[addr] == CachingDiskPageStatus::Writeback);
            assert(false);
        }
    }
    cache_access_reads_in_caching_disk_i_by_domains(
        pre_cache,
        post_cache,
        disk,
        cache_addrs,
        persistent_addrs,
        reads,
        writes,
    );
    assert(reads <= pre_cd.cache);
    assert(CachingDisk::State::next_by(
        pre_cd,
        post_cd,
        CachingDisk::Label::Access{reads, writes},
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);
}

pub proof fn projected_cache_read_only_access_unchanged(
    pre: Cache::State,
    post: Cache::State,
    owned_aus: Set<AU>,
    reads: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        Cache::State::next(
            pre,
            post,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
    ensures
        project_cache_pages(post, owned_aus) =~= project_cache_pages(pre, owned_aus),
        project_cache_status(post, owned_aus) =~= project_cache_status(pre, owned_aus),
{
    let empty_writes = Map::<Address, RawPage>::empty();
    projected_cache_access_effect(pre, post, owned_aus, reads, empty_writes);
    assert_maps_equal!(
        project_cache_pages(pre, owned_aus).union_prefer_right(empty_writes),
        project_cache_pages(pre, owned_aus),
        addr => {}
    );
    assert_maps_equal!(
        project_cache_status(pre, owned_aus).union_prefer_right(
            status_map(empty_writes.dom(), CachingDiskPageStatus::Dirty),
        ),
        project_cache_status(pre, owned_aus),
        addr => {}
    );
}

pub proof fn projected_cache_access_outside_aus_unchanged(
    pre: Cache::State,
    post: Cache::State,
    owned_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Access{reads, writes}),
        writes.dom().disjoint(addresses_in_aus(owned_aus)),
    ensures
        project_cache_pages(post, owned_aus) =~= project_cache_pages(pre, owned_aus),
        project_cache_status(post, owned_aus) =~= project_cache_status(pre, owned_aus),
{
    let lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre, post, lbl);
    pre.build_lookup_map_ensures();
    post.build_lookup_map_ensures();

    assert_maps_equal!(
        project_cache_pages(post, owned_aus),
        project_cache_pages(pre, owned_aus),
        addr => {
            if addresses_in_aus(owned_aus).contains(addr) {
                assert(!writes.contains_key(addr)) by {
                    if writes.contains_key(addr) {
                        assert(writes.dom().contains(addr));
                        assert(false);
                    }
                }
                Cache::State::access_unwritten_addr_unchanged(pre, post, reads, writes, addr);
            }
            if project_cache_pages(post, owned_aus).contains_key(addr) {
                assert(addresses_in_aus(owned_aus).contains(addr));
                assert(cache_filled_addr(post, addr));
                assert(cache_filled_addr(pre, addr));
                assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                assert(post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]]);
            }
            if project_cache_pages(pre, owned_aus).contains_key(addr) {
                assert(addresses_in_aus(owned_aus).contains(addr));
                assert(cache_filled_addr(pre, addr));
                assert(cache_filled_addr(post, addr));
                assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                assert(post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]]);
            }
        }
    );
    assert_maps_equal!(
        project_cache_status(post, owned_aus),
        project_cache_status(pre, owned_aus),
        addr => {
            if addresses_in_aus(owned_aus).contains(addr) {
                assert(!writes.contains_key(addr)) by {
                    if writes.contains_key(addr) {
                        assert(writes.dom().contains(addr));
                        assert(false);
                    }
                }
                Cache::State::access_unwritten_addr_unchanged(pre, post, reads, writes, addr);
            }
            if project_cache_status(post, owned_aus).contains_key(addr) {
                assert(addresses_in_aus(owned_aus).contains(addr));
                assert(cache_filled_addr(post, addr));
                assert(cache_filled_addr(pre, addr));
                assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                assert(post.status_map[post.lookup_map[addr]]
                    == pre.status_map[pre.lookup_map[addr]]);
            }
            if project_cache_status(pre, owned_aus).contains_key(addr) {
                assert(addresses_in_aus(owned_aus).contains(addr));
                assert(cache_filled_addr(pre, addr));
                assert(cache_filled_addr(post, addr));
                assert(post.lookup_map[addr] == pre.lookup_map[addr]);
                assert(post.status_map[post.lookup_map[addr]]
                    == pre.status_map[pre.lookup_map[addr]]);
            }
        }
    );
}

pub proof fn cache_internal_refines_caching_disk_internal_by_domains(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    cache_addrs: Set<Address>,
    persistent_addrs: Set<Address>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
    ensures
        CachingDisk::State::next(
            caching_disk_i_by_domains(pre_cache, disk, cache_addrs, persistent_addrs),
            caching_disk_i_by_domains(post_cache, disk, cache_addrs, persistent_addrs),
            CachingDisk::Label::Internal{},
        ),
{
    let pre_cd = caching_disk_i_by_domains(pre_cache, disk, cache_addrs, persistent_addrs);
    let post_cd = caching_disk_i_by_domains(post_cache, disk, cache_addrs, persistent_addrs);
    Cache::State::inv_next(pre_cache, post_cache, Cache::Label::Internal{});
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
        step,
    );
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert(Cache::State::reserve(pre_cache, post_cache, Cache::Label::Internal{}, new_slots_mapping)) by {
                reveal(Cache::State::reserve);
            }
            let updated_entries = Map::new(
                |slot| new_slots_mapping.contains_key(slot),
                |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
            );
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.status_map == pre_cache.status_map);
            assert_maps_equal!(
                project_cache_pages_by_addrs(post_cache, cache_addrs),
                project_cache_pages_by_addrs(pre_cache, cache_addrs),
                addr => {
                    if project_cache_pages_by_addrs(post_cache, cache_addrs).contains_key(addr) {
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(post_cache, addr));
                        let slot = post_cache.lookup_map[addr];
                        assert(post_cache.entries[slot] is Filled);
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(post_cache.entries[slot] == Entry::Reserved{
                                    addr: new_slots_mapping[slot],
                                });
                                assert(false);
                            }
                        }
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(pre_cache.entries[slot] is Filled);
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == slot) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                        }
                        assert(cache_filled_addr(pre_cache, addr));
                    }
                    if project_cache_pages_by_addrs(pre_cache, cache_addrs).contains_key(addr) {
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        let slot = pre_cache.lookup_map[addr];
                        assert(pre_cache.entries[slot] is Filled);
                        assert(!new_slots_mapping.contains_key(slot)) by {
                            if new_slots_mapping.contains_key(slot) {
                                assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                                assert(pre_cache.entries[slot] is Empty);
                                assert(false);
                            }
                        }
                        assert(!updated_entries.contains_key(slot));
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == slot) by {
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(cache_filled_addr(post_cache, addr));
                    }
                }
            );
            assert_maps_equal!(
                project_cache_status_by_addrs(post_cache, cache_addrs),
                project_cache_status_by_addrs(pre_cache, cache_addrs),
                addr => {
                    if project_cache_status_by_addrs(post_cache, cache_addrs).contains_key(addr) {
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(post_cache, addr));
                        let slot = post_cache.lookup_map[addr];
                        assert(post_cache.entries[slot] is Filled);
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(post_cache.entries[slot] == Entry::Reserved{
                                    addr: new_slots_mapping[slot],
                                });
                                assert(false);
                            }
                        }
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(pre_cache.entries[slot] is Filled);
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == slot) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                        }
                        assert(post_cache.status_map[slot] == pre_cache.status_map[slot]);
                        assert(cache_filled_addr(pre_cache, addr));
                    }
                    if project_cache_status_by_addrs(pre_cache, cache_addrs).contains_key(addr) {
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        let slot = pre_cache.lookup_map[addr];
                        assert(pre_cache.entries[slot] is Filled);
                        assert(!new_slots_mapping.contains_key(slot)) by {
                            if new_slots_mapping.contains_key(slot) {
                                assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                                assert(pre_cache.entries[slot] is Empty);
                                assert(false);
                            }
                        }
                        assert(!updated_entries.contains_key(slot));
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == slot) by {
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(post_cache.status_map[slot] == pre_cache.status_map[slot]);
                        assert(cache_filled_addr(post_cache, addr));
                    }
                }
            );
            assert(pre_cd == post_cd) by {
                assert(pre_cd.cache == post_cd.cache);
                assert(pre_cd.status == post_cd.status);
                assert(pre_cd.persistent == post_cd.persistent);
            }
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::internal_noop(),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        Cache::Step::evict(evicted_slots) => {
            assert(Cache::State::evict(pre_cache, post_cache, Cache::Label::Internal{}, evicted_slots)) by {
                reveal(Cache::State::evict);
            }
            let evicted_map = Map::new(
                |slot: Slot| evicted_slots.contains(slot),
                |slot: Slot| pre_cache.entries[slot].get_addr(),
            );
            let evicted_addrs = evicted_map.values();
            let projected_evicted = evicted_addrs.intersect(pre_cd.cache.dom());
            assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
            assert forall |addr: Address| #[trigger] projected_evicted.contains(addr) implies {
                &&& pre_cd.status.contains_key(addr)
                &&& pre_cd.status[addr] == CachingDiskPageStatus::Clean
            } by {
                assert(evicted_addrs.contains(addr));
                assert(pre_cd.cache.contains_key(addr));
                assert(project_cache_pages_by_addrs(pre_cache, cache_addrs).contains_key(addr));
                let slot = choose |slot: Slot| #![auto] evicted_map.contains_key(slot) && evicted_map[slot] == addr;
                assert(evicted_slots.contains(slot));
                assert(pre_cache.entries[slot] is Filled);
                assert(pre_cache.status_map[slot] is Clean);
                assert(pre_cache.status_map[slot] == CacheStatus::Clean);
                assert(pre_cache.lookup_map.contains_key(addr));
                assert(pre_cache.lookup_map[addr] == slot) by {
                    assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                }
                assert(cache_filled_addr(pre_cache, addr));
                assert(filled_cache_status(pre_cache).contains_key(addr));
                assert(cache_status_i(pre_cache, addr) == CachingDiskPageStatus::Clean);
                assert(filled_cache_status(pre_cache)[addr] == CachingDiskPageStatus::Clean);
                assert(project_cache_status_by_addrs(pre_cache, cache_addrs).contains_key(addr));
            }
            assert_maps_equal!(
                post_cd.cache,
                pre_cd.cache.remove_keys(projected_evicted),
                addr => {
                    if post_cd.cache.contains_key(addr) {
                        assert(project_cache_pages_by_addrs(post_cache, cache_addrs).contains_key(addr));
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(post_cache, addr));
                        assert(!evicted_addrs.contains(addr)) by {
                            if evicted_addrs.contains(addr) {
                                assert(!post_cache.lookup_map.contains_key(addr));
                                assert(cache_filled_addr(post_cache, addr));
                                assert(false);
                            }
                        }
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == post_cache.lookup_map[addr]) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(filled_cache_status(post_cache).contains_key(addr));
                        assert(filled_cache_status(pre_cache).contains_key(addr));
                        assert(filled_cache_status(post_cache)[addr]
                            == filled_cache_status(pre_cache)[addr]);
                        assert(pre_cd.cache.contains_key(addr));
                        assert(!projected_evicted.contains(addr));
                    }
                    if pre_cd.cache.remove_keys(projected_evicted).contains_key(addr) {
                        assert(pre_cd.cache.contains_key(addr));
                        assert(project_cache_pages_by_addrs(pre_cache, cache_addrs).contains_key(addr));
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(!projected_evicted.contains(addr));
                        assert(!evicted_addrs.contains(addr)) by {
                            if evicted_addrs.contains(addr) {
                                assert(projected_evicted.contains(addr));
                                assert(false);
                            }
                        }
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(cache_filled_addr(post_cache, addr));
                        assert(filled_cache_status(pre_cache).contains_key(addr));
                        assert(filled_cache_status(post_cache).contains_key(addr));
                        assert(filled_cache_status(post_cache)[addr]
                            == filled_cache_status(pre_cache)[addr]);
                        assert(post_cd.cache.contains_key(addr));
                    }
                }
            );
            assert_maps_equal!(
                post_cd.status,
                pre_cd.status.remove_keys(projected_evicted),
                addr => {
                    if post_cd.status.contains_key(addr) {
                        assert(project_cache_status_by_addrs(post_cache, cache_addrs).contains_key(addr));
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(post_cache, addr));
                        assert(!evicted_addrs.contains(addr)) by {
                            if evicted_addrs.contains(addr) {
                                assert(!post_cache.lookup_map.contains_key(addr));
                                assert(cache_filled_addr(post_cache, addr));
                                assert(false);
                            }
                        }
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == post_cache.lookup_map[addr]) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(filled_cache_status(post_cache).contains_key(addr));
                        assert(filled_cache_status(pre_cache).contains_key(addr));
                        assert(filled_cache_status(post_cache)[addr]
                            == filled_cache_status(pre_cache)[addr]);
                        assert(pre_cd.status.contains_key(addr));
                        assert(!projected_evicted.contains(addr));
                    }
                    if pre_cd.status.remove_keys(projected_evicted).contains_key(addr) {
                        assert(pre_cd.status.contains_key(addr));
                        assert(project_cache_status_by_addrs(pre_cache, cache_addrs).contains_key(addr));
                        assert(cache_addrs.contains(addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(!projected_evicted.contains(addr));
                        assert(!evicted_addrs.contains(addr)) by {
                            if evicted_addrs.contains(addr) {
                                assert(projected_evicted.contains(addr));
                                assert(false);
                            }
                        }
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(cache_filled_addr(post_cache, addr));
                        assert(filled_cache_status(pre_cache).contains_key(addr));
                        assert(filled_cache_status(post_cache).contains_key(addr));
                        assert(filled_cache_status(post_cache)[addr]
                            == filled_cache_status(pre_cache)[addr]);
                        assert(post_cd.status.contains_key(addr));
                    }
                }
            );
            assert(post_cd.persistent == pre_cd.persistent);
            assert(CachingDisk::State::evict_clean(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                projected_evicted,
            )) by {
                reveal(CachingDisk::State::evict_clean);
            }
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::evict_clean(projected_evicted),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        Cache::Step::noop() => {
            assert(post_cache == pre_cache) by {
                assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                    reveal(Cache::State::noop);
                }
            }
            assert(pre_cd == post_cd);
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::internal_noop(),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_internal_preserves_protected_entries(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    protected_addrs: Set<Address>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        protected_addrs <= pre_cache.lookup_map.dom(),
        forall |addr: Address| #[trigger] protected_addrs.contains(addr) ==> {
            let slot = pre_cache.lookup_map[addr];
            match pre_cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre_cache.status_map[slot] is Writeback,
                _ => false,
            }
        },
    ensures
        forall |addr: Address| #[trigger] protected_addrs.contains(addr) ==> {
            &&& pre_cache.lookup_map.contains_key(addr)
            &&& pre_cache.entries.contains_key(pre_cache.lookup_map[addr])
            &&& post_cache.lookup_map.contains_key(addr)
            &&& post_cache.entries.contains_key(post_cache.lookup_map[addr])
            &&& post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]
            &&& post_cache.entries[post_cache.lookup_map[addr]]
                == pre_cache.entries[pre_cache.lookup_map[addr]]
            &&& post_cache.status_map[post_cache.lookup_map[addr]]
                == pre_cache.status_map[pre_cache.lookup_map[addr]]
        },
{
    Cache::State::inv_next(pre_cache, post_cache, Cache::Label::Internal{});
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
        step,
    );

    assert forall |addr: Address| #[trigger] protected_addrs.contains(addr) implies {
        &&& pre_cache.lookup_map.contains_key(addr)
        &&& pre_cache.entries.contains_key(pre_cache.lookup_map[addr])
        &&& post_cache.lookup_map.contains_key(addr)
        &&& post_cache.entries.contains_key(post_cache.lookup_map[addr])
        &&& post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]
        &&& post_cache.entries[post_cache.lookup_map[addr]]
            == pre_cache.entries[pre_cache.lookup_map[addr]]
        &&& post_cache.status_map[post_cache.lookup_map[addr]]
            == pre_cache.status_map[pre_cache.lookup_map[addr]]
    } by {
        assert(pre_cache.lookup_map.contains_key(addr));
        let pre_slot = pre_cache.lookup_map[addr];
        assert(pre_cache.entries.contains_key(pre_slot)) by {
            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
        }
        assert(match pre_cache.entries[pre_slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && pre_cache.status_map[pre_slot] is Writeback,
            _ => false,
        });

        match step {
            Cache::Step::reserve(new_slots_mapping) => {
                assert(Cache::State::reserve(
                    pre_cache,
                    post_cache,
                    Cache::Label::Internal{},
                    new_slots_mapping,
                )) by {
                    reveal(Cache::State::reserve);
                }
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.status_map == pre_cache.status_map);
                assert(!new_slots_mapping.contains_key(pre_slot)) by {
                    if new_slots_mapping.contains_key(pre_slot) {
                        assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                        assert(pre_cache.entries[pre_slot] is Empty);
                        match pre_cache.entries[pre_slot] {
                            Entry::Loading{..} => {
                                assert(false);
                            },
                            Entry::Filled{..} => {
                                assert(false);
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                }
                assert(!updated_entries.contains_key(pre_slot));
                assert(!new_slots_mapping.invert().contains_key(addr)) by {
                    if new_slots_mapping.invert().contains_key(addr) {
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        assert(new_slots_mapping.values().contains(addr));
                        assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                        assert(pre_cache.lookup_map.dom().contains(addr));
                        assert(false);
                    }
                }
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                assert(post_cache.lookup_map.contains_key(addr));
                assert(post_cache.lookup_map[addr] == pre_slot);
                assert(post_cache.entries[pre_slot] == pre_cache.entries[pre_slot]);
                assert(post_cache.status_map[pre_slot] == pre_cache.status_map[pre_slot]);
            },
            Cache::Step::evict(evicted_slots) => {
                assert(Cache::State::evict(
                    pre_cache,
                    post_cache,
                    Cache::Label::Internal{},
                    evicted_slots,
                )) by {
                    reveal(Cache::State::evict);
                }
                let evicted_addrs = Map::new(
                    |slot: Slot| evicted_slots.contains(slot),
                    |slot: Slot| pre_cache.entries[slot].get_addr(),
                ).values();
                assert(!evicted_slots.contains(pre_slot)) by {
                    if evicted_slots.contains(pre_slot) {
                        assert(pre_cache.entries[pre_slot] is Filled);
                        assert(pre_cache.status_map[pre_slot] is Clean);
                        match pre_cache.entries[pre_slot] {
                            Entry::Loading{..} => {
                                assert(false);
                            },
                            Entry::Filled{..} => {
                                assert(pre_cache.status_map[pre_slot] is Writeback);
                                assert(false);
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                }
                assert(!evicted_addrs.contains(addr)) by {
                    if evicted_addrs.contains(addr) {
                        let evicted_map = Map::new(
                            |slot: Slot| evicted_slots.contains(slot),
                            |slot: Slot| pre_cache.entries[slot].get_addr(),
                        );
                        let slot = choose |slot: Slot| #![auto] {
                            &&& evicted_map.contains_key(slot)
                            &&& evicted_map[slot] == addr
                        };
                        assert(evicted_slots.contains(slot));
                        assert(pre_cache.entries[slot] is Filled);
                        assert(pre_cache.entries[slot].get_addr() == addr);
                        assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                        assert(pre_cache.lookup_map[addr] == slot);
                        assert(slot == pre_slot);
                        assert(false);
                    }
                }
                let updated_entries = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| Entry::Empty,
                );
                let updated_status_map = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| CacheStatus::NotFilled,
                );
                assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
                assert(post_cache.lookup_map.contains_key(addr));
                assert(post_cache.lookup_map[addr] == pre_slot);
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.status_map
                    == pre_cache.status_map.union_prefer_right(updated_status_map));
                assert(!updated_entries.contains_key(pre_slot));
                assert(!updated_status_map.contains_key(pre_slot));
                assert(post_cache.entries[pre_slot] == pre_cache.entries[pre_slot]);
                assert(post_cache.status_map[pre_slot] == pre_cache.status_map[pre_slot]);
            },
            Cache::Step::noop() => {
                assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                    reveal(Cache::State::noop);
                }
                assert(post_cache == pre_cache);
            },
            _ => {
                assert(false);
            },
        }
        assert(post_cache.entries.contains_key(post_cache.lookup_map[addr])) by {
            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
        }
    }
}

pub proof fn cache_internal_post_filled_addr_was_pre_filled(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    addr: Address,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        cache_filled_addr(post_cache, addr),
    ensures
        cache_filled_addr(pre_cache, addr),
        filled_cache_status(pre_cache)
            .contains_key(addr),
        filled_cache_status(post_cache)
            .contains_key(addr),
        filled_cache_status(post_cache)[addr]
            == filled_cache_status(pre_cache)[addr],
        cache_filled_page(post_cache, addr)
            == cache_filled_page(pre_cache, addr),
{
    Cache::State::inv_next(pre_cache, post_cache, Cache::Label::Internal{});
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
        step,
    );
    let post_slot = post_cache.lookup_map[addr];
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert(Cache::State::reserve(
                pre_cache,
                post_cache,
                Cache::Label::Internal{},
                new_slots_mapping,
            )) by {
                reveal(Cache::State::reserve);
            }
            let updated_entries = Map::new(
                |slot| new_slots_mapping.contains_key(slot),
                |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
            );
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(!updated_entries.contains_key(post_slot)) by {
                if updated_entries.contains_key(post_slot) {
                    assert(post_cache.entries[post_slot] == Entry::Reserved{
                        addr: new_slots_mapping[post_slot],
                    });
                    assert(post_cache.entries[post_slot] is Filled);
                    assert(false);
                }
            }
            assert(!new_slots_mapping.invert().contains_key(addr)) by {
                if new_slots_mapping.invert().contains_key(addr) {
                    Cache::State::invert_contains_pair(new_slots_mapping, addr);
                    assert(new_slots_mapping.values().contains(addr));
                    assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                    if pre_cache.lookup_map.contains_key(addr) {
                        assert(false);
                    }
                }
            }
            assert(post_cache.lookup_map
                == pre_cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.lookup_map[addr] == post_slot);
            assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]);
        },
        Cache::Step::evict(evicted_slots) => {
            assert(Cache::State::evict(
                pre_cache,
                post_cache,
                Cache::Label::Internal{},
                evicted_slots,
            )) by {
                reveal(Cache::State::evict);
            }
            let evicted_addrs = Map::new(
                |slot: Slot| evicted_slots.contains(slot),
                |slot: Slot| pre_cache.entries[slot].get_addr(),
            ).values();
            assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.lookup_map[addr] == post_slot);
            assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]) by {
                let updated_entries = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| Entry::Empty,
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(!updated_entries.contains_key(post_slot)) by {
                    if updated_entries.contains_key(post_slot) {
                        assert(post_cache.entries[post_slot] is Empty);
                        assert(post_cache.entries[post_slot] is Filled);
                        assert(false);
                    }
                }
            }
        },
        Cache::Step::noop() => {
            assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                reveal(Cache::State::noop);
            }
            assert(post_cache == pre_cache);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_internal_preserves_clean_filled_addr(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    addr: Address,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        filled_cache_status(post_cache).contains_key(addr),
        filled_cache_status(post_cache)[addr] == CachingDiskPageStatus::Clean,
    ensures
        filled_cache_status(pre_cache).contains_key(addr),
        filled_cache_status(pre_cache)[addr] == CachingDiskPageStatus::Clean,
        cache_filled_page(post_cache, addr) == cache_filled_page(pre_cache, addr),
{
    Cache::State::inv_next(pre_cache, post_cache, Cache::Label::Internal{});
    assert(cache_filled_addr(post_cache, addr));
    cache_internal_post_filled_addr_was_pre_filled(pre_cache, post_cache, addr);
    assert(cache_filled_addr(pre_cache, addr));

    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
        step,
    );
    let post_slot = post_cache.lookup_map[addr];
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert(Cache::State::reserve(
                pre_cache,
                post_cache,
                Cache::Label::Internal{},
                new_slots_mapping,
            )) by {
                reveal(Cache::State::reserve);
            }
            let updated_entries = Map::new(
                |slot| new_slots_mapping.contains_key(slot),
                |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
            );
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.status_map == pre_cache.status_map);
            assert(!updated_entries.contains_key(post_slot)) by {
                if updated_entries.contains_key(post_slot) {
                    assert(post_cache.entries[post_slot] == Entry::Reserved{
                        addr: new_slots_mapping[post_slot],
                    });
                    assert(post_cache.entries[post_slot] is Filled);
                    assert(false);
                }
            }
            assert(post_cache.lookup_map
                == pre_cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.lookup_map[addr] == post_slot);
            assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]);
            assert(pre_cache.status_map[post_slot] == post_cache.status_map[post_slot]);
        },
        Cache::Step::evict(evicted_slots) => {
            assert(Cache::State::evict(
                pre_cache,
                post_cache,
                Cache::Label::Internal{},
                evicted_slots,
            )) by {
                reveal(Cache::State::evict);
            }
            let evicted_addrs = Map::new(
                |slot: Slot| evicted_slots.contains(slot),
                |slot: Slot| pre_cache.entries[slot].get_addr(),
            ).values();
            assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
            assert(!evicted_addrs.contains(addr)) by {
                if evicted_addrs.contains(addr) {
                    assert(!post_cache.lookup_map.contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    assert(false);
                }
            }
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.lookup_map[addr] == post_slot) by {
                pre_cache.build_lookup_map_ensures();
                post_cache.build_lookup_map_ensures();
            }
            assert(!evicted_slots.contains(post_slot)) by {
                if evicted_slots.contains(post_slot) {
                    assert(evicted_addrs.contains(addr));
                    assert(false);
                }
            }
            let updated_entries = Map::new(
                |slot| evicted_slots.contains(slot),
                |slot| Entry::Empty,
            );
            let updated_status_map = Map::new(
                |slot| evicted_slots.contains(slot),
                |slot| CacheStatus::NotFilled,
            );
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.status_map == pre_cache.status_map.union_prefer_right(
                updated_status_map,
            ));
            assert(!updated_entries.contains_key(post_slot));
            assert(!updated_status_map.contains_key(post_slot));
            assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]);
            assert(pre_cache.status_map[post_slot] == post_cache.status_map[post_slot]);
        },
        Cache::Step::noop() => {
            assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                reveal(Cache::State::noop);
            }
            assert(post_cache == pre_cache);
        },
        _ => {
            assert(false);
        },
    }
    assert(cache_filled_page(post_cache, addr) == cache_filled_page(pre_cache, addr));
    assert(filled_cache_status(pre_cache).contains_key(addr));
    assert(filled_cache_status(pre_cache)[addr] == CachingDiskPageStatus::Clean);
}

pub proof fn cache_internal_preserves_readable_on_preserved_filled_addrs(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    protected: Set<Address>,
)
    requires
        pre_cache.inv(),
        protected <= addresses_in_aus(owned_aus),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        forall |addr: Address| {
            &&& #[trigger] protected.contains(addr)
            &&& cache_filled_addr(pre_cache, addr)
        } ==> {
            &&& cache_filled_addr(post_cache, addr)
            &&& cache_filled_page(post_cache, addr) == cache_filled_page(pre_cache, addr)
        },
    ensures
        forall |addr: Address| #[trigger] protected.contains(addr) ==> {
            &&& caching_disk_i(post_cache, disk, owned_aus).readable().contains_key(addr)
                == caching_disk_i(pre_cache, disk, owned_aus).readable().contains_key(addr)
            &&& caching_disk_i(post_cache, disk, owned_aus).readable().contains_key(addr) ==>
                caching_disk_i(post_cache, disk, owned_aus).readable()[addr]
                    == caching_disk_i(pre_cache, disk, owned_aus).readable()[addr]
        },
{
    let pre_cd = caching_disk_i(pre_cache, disk, owned_aus);
    let post_cd = caching_disk_i(post_cache, disk, owned_aus);
    Cache::State::inv_next(pre_cache, post_cache, Cache::Label::Internal{});
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
        step,
    );

    assert forall |addr: Address| #[trigger] protected.contains(addr) implies {
        &&& post_cd.readable().contains_key(addr) == pre_cd.readable().contains_key(addr)
        &&& post_cd.readable().contains_key(addr) ==> post_cd.readable()[addr] == pre_cd.readable()[addr]
    } by {
        assert(addresses_in_aus(owned_aus).contains(addr));
        match step {
            Cache::Step::reserve(new_slots_mapping) => {
                assert(Cache::State::reserve(
                    pre_cache,
                    post_cache,
                    Cache::Label::Internal{},
                    new_slots_mapping,
                )) by {
                    reveal(Cache::State::reserve);
                }
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.status_map == pre_cache.status_map);
                if post_cd.cache.contains_key(addr) {
                    assert(cache_filled_addr(post_cache, addr));
                    let slot = post_cache.lookup_map[addr];
                    assert(!updated_entries.contains_key(slot)) by {
                        if updated_entries.contains_key(slot) {
                            assert(post_cache.entries[slot] is Reserved);
                            assert(post_cache.entries[slot] is Filled);
                            assert(false);
                        }
                    }
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.lookup_map[addr] == slot);
                    assert(pre_cache.entries[slot] == post_cache.entries[slot]);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(pre_cd.cache.contains_key(addr));
                    assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                }
                if pre_cd.cache.contains_key(addr) {
                    assert(cache_filled_addr(pre_cache, addr));
                    let slot = pre_cache.lookup_map[addr];
                    assert(!new_slots_mapping.contains_key(slot)) by {
                        if new_slots_mapping.contains_key(slot) {
                            assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                            assert(pre_cache.entries[slot] is Empty);
                            assert(pre_cache.entries[slot] is Filled);
                            assert(false);
                        }
                    }
                    assert(post_cache.lookup_map.contains_key(addr));
                    assert(post_cache.lookup_map[addr] == slot);
                    assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                    assert(cache_filled_addr(post_cache, addr));
                    assert(post_cd.cache.contains_key(addr));
                    assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                }
                assert(post_cd.persistent.contains_key(addr)
                    == pre_cd.persistent.contains_key(addr));
                if post_cd.persistent.contains_key(addr) {
                    assert(post_cd.persistent[addr] == pre_cd.persistent[addr]);
                }
            },
            Cache::Step::evict(evicted_slots) => {
                assert(Cache::State::evict(
                    pre_cache,
                    post_cache,
                    Cache::Label::Internal{},
                    evicted_slots,
                )) by {
                    reveal(Cache::State::evict);
                }
                let evicted_addrs = Map::new(
                    |slot: Slot| evicted_slots.contains(slot),
                    |slot: Slot| pre_cache.entries[slot].get_addr(),
                ).values();
                let updated_entries = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| Entry::Empty,
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
                if evicted_addrs.contains(addr) {
                    let slot = choose |slot: Slot| evicted_slots.contains(slot)
                        && #[trigger] pre_cache.entries[slot].get_addr() == addr;
                    assert(pre_cache.entries[slot] is Filled);
                    assert(pre_cache.status_map[slot] is Clean);
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.lookup_map[addr] == slot);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(!post_cache.lookup_map.contains_key(addr));
                    assert(cache_filled_addr(post_cache, addr));
                    assert(false);
                } else {
                    if post_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(post_cache, addr));
                        assert(post_cache.lookup_map.contains_key(addr));
                        let slot = post_cache.lookup_map[addr];
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == slot);
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(evicted_slots.contains(slot));
                                assert(evicted_addrs.contains(addr));
                                assert(false);
                            }
                        }
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(pre_cd.cache.contains_key(addr));
                        assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                    }
                    if pre_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(pre_cache, addr));
                        let slot = pre_cache.lookup_map[addr];
                        assert(!evicted_slots.contains(slot)) by {
                            if evicted_slots.contains(slot) {
                                assert(evicted_addrs.contains(addr));
                                assert(false);
                            }
                        }
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == slot);
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(cache_filled_addr(post_cache, addr));
                        assert(post_cd.cache.contains_key(addr));
                        assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                    }
                    assert(post_cd.persistent.contains_key(addr)
                        == pre_cd.persistent.contains_key(addr));
                    if post_cd.persistent.contains_key(addr) {
                        assert(post_cd.persistent[addr] == pre_cd.persistent[addr]);
                    }
                }
            },
            Cache::Step::noop() => {
                assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                    reveal(Cache::State::noop);
                }
                assert(post_cache == pre_cache);
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_internal_preserves_empty_projection(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    aus: Set<AU>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        project_cache_pages(pre_cache, aus) == Map::<Address, RawPage>::empty(),
        project_cache_status(pre_cache, aus) == Map::<Address, CachingDiskPageStatus>::empty(),
    ensures
        project_cache_pages(post_cache, aus) == Map::<Address, RawPage>::empty(),
        project_cache_status(post_cache, aus) == Map::<Address, CachingDiskPageStatus>::empty(),
{
    assert_maps_equal!(
        project_cache_pages(post_cache, aus),
        Map::<Address, RawPage>::empty(),
        addr => {
            if project_cache_pages(post_cache, aus).contains_key(addr) {
                assert(addresses_in_aus(aus).contains(addr));
                assert(cache_filled_addr(post_cache, addr));
                cache_internal_post_filled_addr_was_pre_filled(pre_cache, post_cache, addr);
                assert(project_cache_pages(pre_cache, aus).contains_key(addr));
                assert(false);
            }
        }
    );
    assert_maps_equal!(
        project_cache_status(post_cache, aus),
        Map::<Address, CachingDiskPageStatus>::empty(),
        addr => {
            if project_cache_status(post_cache, aus).contains_key(addr) {
                assert(addresses_in_aus(aus).contains(addr));
                assert(cache_filled_addr(post_cache, addr));
                cache_internal_post_filled_addr_was_pre_filled(pre_cache, post_cache, addr);
                assert(project_cache_status(pre_cache, aus).contains_key(addr));
                assert(false);
            }
        }
    );
}

pub proof fn cache_internal_refines_caching_disk_internal(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
    ensures
        CachingDisk::State::next(
            caching_disk_i(pre_cache, disk, owned_aus),
            caching_disk_i(post_cache, disk, owned_aus),
            CachingDisk::Label::Internal{},
        ),
{
    cache_internal_refines_caching_disk_internal_by_domains(
        pre_cache,
        post_cache,
        disk,
        addresses_in_aus(owned_aus),
        addresses_in_aus(owned_aus),
    );
}

pub proof fn cache_disk_ops_begin_refines_caching_disk_internal(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    requests: Set<DiskRequest>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests, responses: Map::empty()},
        ),
    ensures
        CachingDisk::State::next(
            caching_disk_i(pre_cache, disk, owned_aus),
            caching_disk_i(post_cache, disk, owned_aus),
            CachingDisk::Label::Internal{},
        ),
        caching_disk_i(post_cache, disk, owned_aus).readable()
            == caching_disk_i(pre_cache, disk, owned_aus).readable(),
{
    let lbl = Cache::Label::DiskOps{requests, responses: Map::empty()};
    let pre_cd = caching_disk_i(pre_cache, disk, owned_aus);
    let post_cd = caching_disk_i(post_cache, disk, owned_aus);
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(pre_cache, post_cache, lbl, step);
    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(Cache::State::load_initiate(
                pre_cache,
                post_cache,
                lbl,
                new_slots_mapping,
            )) by {
                reveal(Cache::State::load_initiate);
            }
            let updated_entries = Map::new(
                |slot| new_slots_mapping.contains_key(slot),
                |slot| Entry::Loading{addr: new_slots_mapping[slot]},
            );
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.status_map == pre_cache.status_map);
            assert_maps_equal!(
                project_cache_pages(post_cache, owned_aus),
                project_cache_pages(pre_cache, owned_aus),
                addr => {
                    if project_cache_pages(post_cache, owned_aus).contains_key(addr) {
                        assert(addresses_in_aus(owned_aus).contains(addr));
                        assert(cache_filled_addr(post_cache, addr));
                        let slot = post_cache.lookup_map[addr];
                        assert(post_cache.entries[slot] is Filled);
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(post_cache.entries[slot] == Entry::Loading{
                                    addr: new_slots_mapping[slot],
                                });
                                assert(false);
                            }
                        }
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(pre_cache.entries[slot] is Filled);
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == slot) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                        }
                        assert(cache_filled_addr(pre_cache, addr));
                    }
                    if project_cache_pages(pre_cache, owned_aus).contains_key(addr) {
                        assert(addresses_in_aus(owned_aus).contains(addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        let slot = pre_cache.lookup_map[addr];
                        assert(pre_cache.entries[slot] is Filled);
                        assert(!new_slots_mapping.contains_key(slot)) by {
                            if new_slots_mapping.contains_key(slot) {
                                assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                                assert(pre_cache.entries[slot] is Empty);
                                assert(false);
                            }
                        }
                        assert(!updated_entries.contains_key(slot));
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == slot) by {
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(cache_filled_addr(post_cache, addr));
                    }
                }
            );
            assert_maps_equal!(
                project_cache_status(post_cache, owned_aus),
                project_cache_status(pre_cache, owned_aus),
                addr => {
                    if project_cache_status(post_cache, owned_aus).contains_key(addr) {
                        assert(addresses_in_aus(owned_aus).contains(addr));
                        assert(cache_filled_addr(post_cache, addr));
                        let slot = post_cache.lookup_map[addr];
                        assert(post_cache.entries[slot] is Filled);
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(post_cache.entries[slot] == Entry::Loading{
                                    addr: new_slots_mapping[slot],
                                });
                                assert(false);
                            }
                        }
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(pre_cache.entries[slot] is Filled);
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == slot) by {
                            assert(pre_cache.build_lookup_map_props(pre_cache.lookup_map));
                        }
                        assert(post_cache.status_map[slot] == pre_cache.status_map[slot]);
                        assert(cache_filled_addr(pre_cache, addr));
                    }
                    if project_cache_status(pre_cache, owned_aus).contains_key(addr) {
                        assert(addresses_in_aus(owned_aus).contains(addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        let slot = pre_cache.lookup_map[addr];
                        assert(pre_cache.entries[slot] is Filled);
                        assert(!new_slots_mapping.contains_key(slot)) by {
                            if new_slots_mapping.contains_key(slot) {
                                assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                                assert(pre_cache.entries[slot] is Empty);
                                assert(false);
                            }
                        }
                        assert(!updated_entries.contains_key(slot));
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(post_cache.lookup_map.contains_key(addr));
                        assert(post_cache.lookup_map[addr] == slot) by {
                            assert(post_cache.build_lookup_map_props(post_cache.lookup_map));
                        }
                        assert(post_cache.status_map[slot] == pre_cache.status_map[slot]);
                        assert(cache_filled_addr(post_cache, addr));
                    }
                }
            );
            assert(pre_cd == post_cd) by {
                assert(pre_cd.cache == post_cd.cache);
                assert(pre_cd.status == post_cd.status);
                assert(pre_cd.persistent == post_cd.persistent);
            }
            assert(post_cd.readable() == pre_cd.readable());
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::internal_noop(),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        Cache::Step::writeback_initiate() => {
            assert(Cache::State::writeback_initiate(pre_cache, post_cache, lbl)) by {
                reveal(Cache::State::writeback_initiate);
            }
            let writeback_addrs = Set::new(|addr: Address| {
                &&& addresses_in_aus(owned_aus).contains(addr)
                &&& exists |req: DiskRequest| {
                    &&& #[trigger] requests.contains(req)
                    &&& req is WriteReq
                    &&& req->to == addr
                }
            });
            let writeback_slots = Map::new(
                |req: DiskRequest| requests.contains(req),
                |req: DiskRequest| pre_cache.lookup_map[req->to],
            ).values();
            let updated_status = Map::new(
                |slot| writeback_slots.contains(slot),
                |slot| CacheStatus::Writeback{},
            );
            assert(post_cache.entries == pre_cache.entries);
            assert(post_cache.lookup_map == pre_cache.lookup_map);
            assert(post_cache.status_map == pre_cache.status_map.union_prefer_right(
                updated_status,
            ));
            assert(pre_cd.all_status(writeback_addrs, CachingDiskPageStatus::Dirty)) by {
                assert forall |addr: Address| #[trigger] writeback_addrs.contains(addr)
                    implies {
                        &&& pre_cd.status.contains_key(addr)
                        &&& pre_cd.status[addr] == CachingDiskPageStatus::Dirty
                    } by {
                    let req = choose |req: DiskRequest| {
                        &&& #[trigger] requests.contains(req)
                        &&& req is WriteReq
                        &&& req->to == addr
                    };
                    assert(pre_cache.valid_writeback_requests(requests));
                    assert(pre_cache.lookup_map.contains_key(addr));
                    let slot = pre_cache.lookup_map[addr];
                    assert(pre_cache.entries[slot] == Entry::Filled{addr, data: req->data});
                    assert(pre_cache.status_map[slot] is Dirty);
                    assert(pre_cache.status_map[slot] == CacheStatus::Dirty);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(project_cache_status(pre_cache, owned_aus).contains_key(addr));
                    assert(cache_status_i(pre_cache, addr) == CachingDiskPageStatus::Dirty);
                }
            }
            assert(post_cd.cache == pre_cd.cache) by {
                assert_maps_equal!(post_cd.cache, pre_cd.cache, addr => {
                    if post_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(post_cache, addr));
                        assert(cache_filled_addr(pre_cache, addr));
                    }
                    if pre_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(cache_filled_addr(post_cache, addr));
                    }
                });
            }
            assert(post_cd.persistent == pre_cd.persistent);
            assert(post_cd.status == pre_cd.status.union_prefer_right(
                status_map(writeback_addrs, CachingDiskPageStatus::Writeback),
            )) by {
                assert_maps_equal!(
                    post_cd.status,
                    pre_cd.status.union_prefer_right(
                        status_map(writeback_addrs, CachingDiskPageStatus::Writeback),
                    ),
                    addr => {
                        if writeback_addrs.contains(addr) {
                            let req = choose |req: DiskRequest| {
                                &&& #[trigger] requests.contains(req)
                                &&& req is WriteReq
                                &&& req->to == addr
                            };
                            assert(pre_cache.valid_writeback_requests(requests));
                            assert(pre_cache.lookup_map.contains_key(addr));
                            let slot = pre_cache.lookup_map[addr];
                            assert(Map::new(
                                |req: DiskRequest| requests.contains(req),
                                |req: DiskRequest| pre_cache.lookup_map[req->to],
                            ).contains_key(req));
                            assert(Map::new(
                                |req: DiskRequest| requests.contains(req),
                                |req: DiskRequest| pre_cache.lookup_map[req->to],
                            )[req] == slot);
                            assert(writeback_slots.contains(slot));
                            assert(updated_status.contains_key(slot));
                            assert(post_cache.status_map[slot] == CacheStatus::Writeback);
                            assert(cache_filled_addr(post_cache, addr));
                            assert(project_cache_status(post_cache, owned_aus)[addr]
                                == CachingDiskPageStatus::Writeback);
                        } else {
                            if post_cd.status.contains_key(addr) {
                                assert(cache_filled_addr(post_cache, addr));
                                assert(cache_filled_addr(pre_cache, addr));
                                let slot = pre_cache.lookup_map[addr];
                                assert(!updated_status.contains_key(slot)) by {
                                    if updated_status.contains_key(slot) {
                                        let req = choose |req: DiskRequest| {
                                            &&& #[trigger] requests.contains(req)
                                            &&& pre_cache.lookup_map[req->to] == slot
                                        };
                                        assert(pre_cache.valid_writeback_requests(requests));
                                        assert(req is WriteReq);
                                        assert(pre_cache.lookup_map[req->to]
                                            == pre_cache.lookup_map[addr]);
                                        assert(pre_cache.lookup_map.is_injective());
                                        assert(req->to == addr);
                                        assert(writeback_addrs.contains(addr));
                                        assert(false);
                                    }
                                }
                                assert(post_cache.status_map[slot]
                                    == pre_cache.status_map[slot]);
                            }
                            if pre_cd.status.union_prefer_right(
                                status_map(writeback_addrs, CachingDiskPageStatus::Writeback),
                            ).contains_key(addr) {
                                if status_map(
                                    writeback_addrs,
                                    CachingDiskPageStatus::Writeback,
                                ).contains_key(addr) {
                                    assert(writeback_addrs.contains(addr));
                                    assert(false);
                                } else {
                                    assert(pre_cd.status.contains_key(addr));
                                    assert(cache_filled_addr(pre_cache, addr));
                                    assert(cache_filled_addr(post_cache, addr));
                                    let slot = pre_cache.lookup_map[addr];
                                    assert(!updated_status.contains_key(slot)) by {
                                        if updated_status.contains_key(slot) {
                                            let req = choose |req: DiskRequest| {
                                                &&& #[trigger] requests.contains(req)
                                                &&& pre_cache.lookup_map[req->to] == slot
                                            };
                                            assert(pre_cache.valid_writeback_requests(requests));
                                            assert(req is WriteReq);
                                            assert(pre_cache.lookup_map[req->to]
                                                == pre_cache.lookup_map[addr]);
                                            assert(pre_cache.lookup_map.is_injective());
                                            assert(req->to == addr);
                                            assert(writeback_addrs.contains(addr));
                                            assert(false);
                                        }
                                    }
                                    assert(post_cache.status_map[slot]
                                        == pre_cache.status_map[slot]);
                                }
                            }
                        }
                    }
                );
            }
            assert(CachingDisk::State::begin_writeback(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                writeback_addrs,
            )) by {
                reveal(CachingDisk::State::begin_writeback);
            }
            assert(post_cd.readable() == pre_cd.readable()) by {
                assert(post_cd.cache == pre_cd.cache);
                assert(post_cd.persistent == pre_cd.persistent);
            }
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::begin_writeback(writeback_addrs),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_disk_ops_begin_preserves_filled_page(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    requests: Set<DiskRequest>,
    addr: Address,
)
    requires
        pre_cache.inv(),
        cache_filled_addr(pre_cache, addr),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests, responses: Map::empty()},
        ),
    ensures
        cache_filled_addr(post_cache, addr),
        cache_filled_page(post_cache, addr) == cache_filled_page(pre_cache, addr),
{
    let lbl = Cache::Label::DiskOps{requests, responses: Map::empty()};
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(pre_cache, post_cache, lbl, step);
    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(Cache::State::load_initiate(
                pre_cache,
                post_cache,
                lbl,
                new_slots_mapping,
            )) by {
                reveal(Cache::State::load_initiate);
            }
            let slot = pre_cache.lookup_map[addr];
            assert(!new_slots_mapping.contains_key(slot)) by {
                if new_slots_mapping.contains_key(slot) {
                    assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                    assert(pre_cache.entries[slot] is Empty);
                    assert(pre_cache.entries[slot] is Filled);
                    assert(false);
                }
            }
            assert(!new_slots_mapping.contains_value(addr)) by {
                assert(pre_cache.valid_new_slots_mapping(new_slots_mapping));
                assert(pre_cache.lookup_map.contains_key(addr));
            }
            assert(post_cache.lookup_map.contains_key(addr));
            assert(post_cache.lookup_map[addr] == slot) by {
                assert(post_cache.lookup_map == pre_cache.lookup_map.union_prefer_right(
                    new_slots_mapping.invert(),
                ));
            }
            assert(post_cache.entries[slot] == pre_cache.entries[slot]) by {
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(!updated_entries.contains_key(slot));
            }
            assert(cache_filled_addr(post_cache, addr));
        },
        Cache::Step::writeback_initiate() => {
            assert(Cache::State::writeback_initiate(pre_cache, post_cache, lbl)) by {
                reveal(Cache::State::writeback_initiate);
            }
            assert(post_cache.entries == pre_cache.entries);
            assert(post_cache.lookup_map == pre_cache.lookup_map);
            assert(cache_filled_addr(post_cache, addr));
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_disk_ops_end_refines_caching_disk_internal(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    responses: Map<Address, DiskResponse>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses},
        ),
        forall |addr: Address| {
            &&& #[trigger] responses.contains_key(addr)
            &&& addresses_in_aus(owned_aus).contains(addr)
        } ==> {
            &&& responses[addr] is ReadResp ==> {
                disk.content.contains_key(addr) ==> responses[addr]->data == disk.content[addr]
            }
            &&& responses[addr] is WriteResp ==> {
                &&& disk.content.contains_key(addr)
                &&& cache_filled_addr(pre_cache, addr)
                &&& disk.content[addr] == cache_filled_page(pre_cache, addr)
            }
        },
    ensures
        CachingDisk::State::next(
            caching_disk_i(pre_cache, disk, owned_aus),
            caching_disk_i(post_cache, disk, owned_aus),
            CachingDisk::Label::Internal{},
        ),
{
    let lbl = Cache::Label::DiskOps{requests: Set::empty(), responses};
    let pre_cd = caching_disk_i(pre_cache, disk, owned_aus);
    let post_cd = caching_disk_i(post_cache, disk, owned_aus);
    let owned_addrs = addresses_in_aus(owned_aus);
    let addrs = responses.dom() * owned_addrs;

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(pre_cache, post_cache, lbl, step);
    match step {
        Cache::Step::load_complete() => {
            assert(Cache::State::load_complete(pre_cache, post_cache, lbl)) by {
                reveal(Cache::State::load_complete);
            }
            let slot_addr_map = pre_cache.lookup_map.restrict(responses.dom()).invert();
            let updated_entries = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Entry::Filled{
                    addr: slot_addr_map[slot],
                    data: responses[slot_addr_map[slot]]->data,
                },
            );
            let updated_status = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| CacheStatus::Clean,
            );
            assert(post_cache.lookup_map == pre_cache.lookup_map);
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.status_map == pre_cache.status_map.union_prefer_right(
                updated_status,
            ));
            Cache::State::inv_next(pre_cache, post_cache, lbl);
            pre_cache.build_lookup_map_ensures();
            post_cache.build_lookup_map_ensures();
            let loaded = Map::new(
                |addr: Address| addrs.contains(addr),
                |addr: Address| responses[addr]->data,
            );
            assert(addrs.disjoint(pre_cd.cache.dom())) by {
                assert forall |addr: Address| #[trigger] addrs.contains(addr)
                    implies !pre_cd.cache.dom().contains(addr) by {
                    assert(responses.contains_key(addr));
                    assert(owned_addrs.contains(addr));
                    assert(pre_cache.valid_load_responses(responses));
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.entries[pre_cache.lookup_map[addr]] is Loading);
                    if pre_cd.cache.dom().contains(addr) {
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(pre_cache.entries[pre_cache.lookup_map[addr]] is Filled);
                        assert(false);
                    }
                }
            }
            assert(post_cd.persistent == pre_cd.persistent);
            assert(post_cd.cache == pre_cd.cache.union_prefer_right(loaded)) by {
                assert_maps_equal!(
                    post_cd.cache,
                    pre_cd.cache.union_prefer_right(loaded),
                    addr => {
                        if responses.contains_key(addr) && owned_addrs.contains(addr) {
                            assert(addrs.contains(addr));
                            assert(loaded.contains_key(addr));
                            assert(pre_cache.lookup_map.contains_key(addr));
                            let slot = pre_cache.lookup_map[addr];
                            assert(pre_cache.valid_load_responses(responses));
                            assert(pre_cache.entries[slot] is Loading);
                            assert(slot_addr_map.contains_key(slot)) by {
                                let restricted = pre_cache.lookup_map.restrict(responses.dom());
                                assert(restricted.contains_key(addr));
                                assert(restricted[addr] == slot);
                                Cache::State::invert_contains_pair(restricted, slot);
                            }
                            assert(slot_addr_map[slot] == addr);
                            assert(updated_entries.contains_key(slot));
                            assert(post_cache.entries[slot] == Entry::Filled{
                                addr,
                                data: responses[addr]->data,
                            });
                            assert(responses[addr] is ReadResp);
                            assert(loaded[addr] == responses[addr]->data);
                            assert(post_cd.cache[addr] == loaded[addr]);
                        } else {
                            if post_cd.cache.contains_key(addr) {
                                assert(owned_addrs.contains(addr));
                                assert(cache_filled_addr(post_cache, addr));
                                if cache_filled_addr(pre_cache, addr) {
                                    assert(post_cache.lookup_map[addr]
                                        == pre_cache.lookup_map[addr]);
                                } else {
                                    let slot = post_cache.lookup_map[addr];
                                    assert(updated_entries.contains_key(slot));
                                    assert(slot_addr_map.contains_key(slot));
                                    let loaded_addr = slot_addr_map[slot];
                                    assert(responses.contains_key(loaded_addr));
                                    assert(post_cache.entries[slot] == Entry::Filled{
                                        addr: loaded_addr,
                                        data: responses[loaded_addr]->data,
                                    });
                                    assert(loaded_addr == addr);
                                    assert(responses.contains_key(addr));
                                    assert(false);
                                }
                            }
                            if pre_cd.cache.union_prefer_right(loaded).contains_key(addr) {
                                if loaded.contains_key(addr) {
                                    assert(addrs.contains(addr));
                                    assert(responses.contains_key(addr));
                                    assert(owned_addrs.contains(addr));
                                    assert(false);
                                } else {
                                    assert(pre_cd.cache.contains_key(addr));
                                    assert(cache_filled_addr(pre_cache, addr));
                                    assert(cache_filled_addr(post_cache, addr));
                                    assert(post_cache.lookup_map[addr]
                                        == pre_cache.lookup_map[addr]);
                                }
                            }
                        }
                    }
                );
            }
            assert(post_cd.status == pre_cd.status.union_prefer_right(
                status_map(addrs, CachingDiskPageStatus::Clean),
            )) by {
                assert_maps_equal!(
                    post_cd.status,
                    pre_cd.status.union_prefer_right(
                        status_map(addrs, CachingDiskPageStatus::Clean),
                    ),
                    addr => {
                        if responses.contains_key(addr) && owned_addrs.contains(addr) {
                            assert(addrs.contains(addr));
                            assert(pre_cache.lookup_map.contains_key(addr));
                            let slot = pre_cache.lookup_map[addr];
                            assert(slot_addr_map.contains_key(slot)) by {
                                let restricted = pre_cache.lookup_map.restrict(responses.dom());
                                assert(restricted.contains_key(addr));
                                assert(restricted[addr] == slot);
                                Cache::State::invert_contains_pair(restricted, slot);
                            }
                            assert(updated_status.contains_key(slot));
                            assert(post_cache.status_map[slot] == CacheStatus::Clean);
                            assert(project_cache_status(post_cache, owned_aus)[addr]
                                == CachingDiskPageStatus::Clean);
                        } else {
                            if post_cd.status.contains_key(addr) {
                                assert(owned_addrs.contains(addr));
                                assert(cache_filled_addr(post_cache, addr));
                                if cache_filled_addr(pre_cache, addr) {
                                    assert(post_cache.lookup_map[addr]
                                        == pre_cache.lookup_map[addr]);
                                    let slot = pre_cache.lookup_map[addr];
                                    assert(!updated_status.contains_key(slot)) by {
                                        if updated_status.contains_key(slot) {
                                            assert(slot_addr_map.contains_key(slot));
                                            let loaded_addr = slot_addr_map[slot];
                                            assert(responses.contains_key(loaded_addr));
                                            assert(pre_cache.lookup_map[loaded_addr] == slot) by {
                                                Cache::State::invert_contains_pair(
                                                    pre_cache.lookup_map.restrict(
                                                        responses.dom(),
                                                    ),
                                                    slot,
                                                );
                                            }
                                            assert(pre_cache.lookup_map[addr] == slot);
                                            assert(loaded_addr == addr) by {
                                                assert(pre_cache.lookup_map.is_injective());
                                            }
                                            assert(responses.contains_key(addr));
                                            assert(false);
                                        }
                                    }
                                    assert(post_cache.status_map[post_cache.lookup_map[addr]]
                                        == pre_cache.status_map[pre_cache.lookup_map[addr]]);
                                } else {
                                    let slot = post_cache.lookup_map[addr];
                                    assert(updated_status.contains_key(slot));
                                    assert(slot_addr_map.contains_key(slot));
                                    let loaded_addr = slot_addr_map[slot];
                                    assert(responses.contains_key(loaded_addr));
                                    assert(loaded_addr == addr);
                                    assert(responses.contains_key(addr));
                                    assert(false);
                                }
                            }
                            if pre_cd.status.union_prefer_right(
                                status_map(addrs, CachingDiskPageStatus::Clean),
                            ).contains_key(addr) {
                                if status_map(
                                    addrs,
                                    CachingDiskPageStatus::Clean,
                                ).contains_key(addr) {
                                    assert(addrs.contains(addr));
                                    assert(responses.contains_key(addr));
                                    assert(owned_addrs.contains(addr));
                                    assert(false);
                                } else {
                                    assert(pre_cd.status.contains_key(addr));
                                    assert(cache_filled_addr(pre_cache, addr));
                                    assert(cache_filled_addr(post_cache, addr));
                                    assert(post_cache.lookup_map[addr]
                                        == pre_cache.lookup_map[addr]);
                                }
                            }
                        }
                    }
                );
            }
            assert(loaded.dom() =~= addrs) by {
                assert forall |addr: Address| #[trigger] loaded.dom().contains(addr)
                    implies addrs.contains(addr) by {
                    assert(loaded.contains_key(addr));
                }
                assert forall |addr: Address| #[trigger] addrs.contains(addr)
                    implies loaded.dom().contains(addr) by {
                    assert(loaded.contains_key(addr));
                }
            }
            assert(status_map(loaded.dom(), CachingDiskPageStatus::Clean)
                == status_map(addrs, CachingDiskPageStatus::Clean)) by {
                assert_maps_equal!(
                    status_map(loaded.dom(), CachingDiskPageStatus::Clean),
                    status_map(addrs, CachingDiskPageStatus::Clean),
                    addr => {}
                );
            }
            assert forall |addr: Address| #[trigger] loaded.contains_key(addr)
                && pre_cd.persistent.contains_key(addr)
                implies loaded[addr] == pre_cd.persistent[addr] by {
                assert(addrs.contains(addr));
                assert(responses.contains_key(addr));
                assert(owned_addrs.contains(addr));
                assert(responses[addr] is ReadResp);
                assert(project_persistent(disk, owned_aus).contains_key(addr));
                assert(disk.content.contains_key(addr));
                assert(pre_cd.persistent[addr] == disk.content[addr]);
                assert(responses[addr]->data == disk.content[addr]);
                assert(loaded[addr] == responses[addr]->data);
            }
            assert(CachingDisk::State::load(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                loaded,
            )) by {
                reveal(CachingDisk::State::load);
            }
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::load(loaded),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        Cache::Step::writeback_complete() => {
            assert(Cache::State::writeback_complete(pre_cache, post_cache, lbl)) by {
                reveal(Cache::State::writeback_complete);
            }
            let resp_slots = pre_cache.lookup_map.restrict(responses.dom()).values();
            let updated_status = Map::new(
                |slot| resp_slots.contains(slot),
                |slot| CacheStatus::Clean,
            );
            assert(post_cache.entries == pre_cache.entries);
            assert(post_cache.lookup_map == pre_cache.lookup_map);
            assert(post_cache.status_map == pre_cache.status_map.union_prefer_right(
                updated_status,
            ));
            Cache::State::inv_next(pre_cache, post_cache, lbl);
            pre_cache.build_lookup_map_ensures();
            post_cache.build_lookup_map_ensures();
            assert(addrs <= pre_cd.cache.dom()) by {
                assert forall |addr: Address| #[trigger] addrs.contains(addr)
                    implies pre_cd.cache.dom().contains(addr) by {
                    assert(responses.contains_key(addr));
                    assert(owned_addrs.contains(addr));
                    assert(pre_cache.valid_writeback_responses(responses));
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.entries[pre_cache.lookup_map[addr]] is Filled);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(project_cache_pages(pre_cache, owned_aus).contains_key(addr));
                }
            }
            assert(pre_cd.all_cleanable(addrs)) by {
                assert forall |addr: Address| #[trigger] addrs.contains(addr) implies {
                    &&& pre_cd.status.contains_key(addr)
                    &&& (pre_cd.status[addr] == CachingDiskPageStatus::Writeback
                        || pre_cd.status[addr] == CachingDiskPageStatus::Clean)
                } by {
                    assert(responses.contains_key(addr));
                    assert(owned_addrs.contains(addr));
                    assert(pre_cache.valid_writeback_responses(responses));
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.status_map[pre_cache.lookup_map[addr]] is Writeback);
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(project_cache_status(pre_cache, owned_aus).contains_key(addr));
                    assert(pre_cd.status[addr] == CachingDiskPageStatus::Writeback);
                }
            }
            assert(pre_cd.persisted(addrs)) by {
                assert forall |addr: Address| #[trigger] addrs.contains(addr)
                    && pre_cd.status[addr] == CachingDiskPageStatus::Writeback implies {
                    &&& pre_cd.cache.contains_key(addr)
                    &&& pre_cd.persistent.contains_key(addr)
                    &&& pre_cd.persistent[addr] == pre_cd.cache[addr]
                } by {
                    assert(responses.contains_key(addr));
                    assert(owned_addrs.contains(addr));
                    assert(disk.content.contains_key(addr));
                    assert(disk.content[addr] == cache_filled_page(pre_cache, addr));
                }
            }
            assert(post_cd.cache == pre_cd.cache) by {
                assert_maps_equal!(post_cd.cache, pre_cd.cache, addr => {
                    if post_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(post_cache, addr));
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                        assert(post_cache.entries[post_cache.lookup_map[addr]]
                            == pre_cache.entries[pre_cache.lookup_map[addr]]);
                    }
                    if pre_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(cache_filled_addr(post_cache, addr));
                        assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                        assert(post_cache.entries[post_cache.lookup_map[addr]]
                            == pre_cache.entries[pre_cache.lookup_map[addr]]);
                    }
                });
            }
            assert(post_cd.persistent == pre_cd.persistent);
            assert(post_cd.status == pre_cd.status.union_prefer_right(
                status_map(addrs, CachingDiskPageStatus::Clean),
            )) by {
                assert_maps_equal!(
                    post_cd.status,
                    pre_cd.status.union_prefer_right(
                        status_map(addrs, CachingDiskPageStatus::Clean),
                    ),
                    addr => {
                        if responses.contains_key(addr) && owned_addrs.contains(addr) {
                            assert(addrs.contains(addr));
                            assert(pre_cache.lookup_map.contains_key(addr));
                            let slot = pre_cache.lookup_map[addr];
                            let restricted = pre_cache.lookup_map.restrict(responses.dom());
                            assert(restricted.contains_key(addr));
                            assert(restricted[addr] == slot);
                            assert(restricted.values().contains(slot));
                            assert(updated_status.contains_key(slot));
                            assert(post_cache.status_map[slot] == CacheStatus::Clean);
                            assert(cache_filled_addr(post_cache, addr));
                            assert(project_cache_status(post_cache, owned_aus)[addr]
                                == CachingDiskPageStatus::Clean);
                        } else {
                            if post_cd.status.contains_key(addr) {
                                assert(cache_filled_addr(post_cache, addr));
                                assert(cache_filled_addr(pre_cache, addr));
                                assert(post_cache.lookup_map[addr] == pre_cache.lookup_map[addr]);
                                let slot = pre_cache.lookup_map[addr];
                                assert(!updated_status.contains_key(slot)) by {
                                    if updated_status.contains_key(slot) {
                                        assert(resp_slots.contains(slot));
                                        let restricted = pre_cache.lookup_map.restrict(
                                            responses.dom(),
                                        );
                                        let response_addr = choose |a: Address|
                                            restricted.contains_key(a)
                                                && #[trigger] restricted[a] == slot;
                                        assert(responses.contains_key(response_addr));
                                        assert(pre_cache.lookup_map[response_addr] == slot);
                                        assert(pre_cache.lookup_map[addr] == slot);
                                        assert(response_addr == addr) by {
                                            assert(pre_cache.lookup_map.is_injective());
                                        }
                                        assert(responses.contains_key(addr));
                                        assert(false);
                                    }
                                }
                                assert(post_cache.status_map[post_cache.lookup_map[addr]]
                                    == pre_cache.status_map[pre_cache.lookup_map[addr]]);
                            }
                            if pre_cd.status.union_prefer_right(
                                status_map(addrs, CachingDiskPageStatus::Clean),
                            ).contains_key(addr) {
                                if status_map(
                                    addrs,
                                    CachingDiskPageStatus::Clean,
                                ).contains_key(addr) {
                                    assert(addrs.contains(addr));
                                    assert(responses.contains_key(addr));
                                    assert(owned_addrs.contains(addr));
                                    assert(false);
                                } else {
                                    assert(pre_cd.status.contains_key(addr));
                                    assert(cache_filled_addr(pre_cache, addr));
                                    assert(cache_filled_addr(post_cache, addr));
                                    assert(post_cache.lookup_map[addr]
                                        == pre_cache.lookup_map[addr]);
                                    let slot = pre_cache.lookup_map[addr];
                                    assert(!updated_status.contains_key(slot)) by {
                                        if updated_status.contains_key(slot) {
                                            assert(resp_slots.contains(slot));
                                            let restricted = pre_cache.lookup_map.restrict(
                                                responses.dom(),
                                            );
                                            let response_addr = choose |a: Address|
                                                restricted.contains_key(a)
                                                    && #[trigger] restricted[a] == slot;
                                            assert(responses.contains_key(response_addr));
                                            assert(pre_cache.lookup_map[response_addr] == slot);
                                            assert(pre_cache.lookup_map[addr] == slot);
                                            assert(response_addr == addr) by {
                                                assert(pre_cache.lookup_map.is_injective());
                                            }
                                            assert(responses.contains_key(addr));
                                            assert(false);
                                        }
                                    }
                                    assert(post_cache.status_map[post_cache.lookup_map[addr]]
                                        == pre_cache.status_map[pre_cache.lookup_map[addr]]);
                                }
                            }
                        }
                    }
                );
            }
            assert(CachingDisk::State::mark_clean(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                addrs,
            )) by {
                reveal(CachingDisk::State::mark_clean);
            }
            assert(CachingDisk::State::next_by(
                pre_cd,
                post_cd,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::mark_clean(addrs),
            )) by {
                reveal(CachingDisk::State::next_by);
            }
            reveal(CachingDisk::State::next);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_disk_ops_end_preserves_readable_on_addrs(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    responses: Map<Address, DiskResponse>,
    protected: Set<Address>,
)
    requires
        pre_cache.inv(),
        protected <= addresses_in_aus(owned_aus),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses},
        ),
        forall |addr: Address| {
            &&& #[trigger] responses.contains_key(addr)
            &&& protected.contains(addr)
            &&& responses[addr] is ReadResp
        } ==> false,
    ensures
        forall |addr: Address| #[trigger] protected.contains(addr) ==> {
            &&& caching_disk_i(post_cache, disk, owned_aus).readable().contains_key(addr)
                == caching_disk_i(pre_cache, disk, owned_aus).readable().contains_key(addr)
            &&& caching_disk_i(post_cache, disk, owned_aus).readable().contains_key(addr) ==>
                caching_disk_i(post_cache, disk, owned_aus).readable()[addr]
                    == caching_disk_i(pre_cache, disk, owned_aus).readable()[addr]
        },
{
    let lbl = Cache::Label::DiskOps{requests: Set::empty(), responses};
    let pre_cd = caching_disk_i(pre_cache, disk, owned_aus);
    let post_cd = caching_disk_i(post_cache, disk, owned_aus);
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(pre_cache, post_cache, lbl, step);

    assert forall |addr: Address| #[trigger] protected.contains(addr) implies {
        &&& post_cd.readable().contains_key(addr) == pre_cd.readable().contains_key(addr)
        &&& post_cd.readable().contains_key(addr) ==> post_cd.readable()[addr] == pre_cd.readable()[addr]
    } by {
        assert(addresses_in_aus(owned_aus).contains(addr));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre_cache, post_cache, lbl)) by {
                    reveal(Cache::State::load_complete);
                }
                let slot_addr_map = pre_cache.lookup_map.restrict(responses.dom()).invert();
                let updated_entries = Map::new(
                    |slot| slot_addr_map.contains_key(slot),
                    |slot| Entry::Filled{
                        addr: slot_addr_map[slot],
                        data: responses[slot_addr_map[slot]]->data,
                    },
                );
                assert(post_cache.lookup_map == pre_cache.lookup_map);
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                if responses.contains_key(addr) {
                    assert(pre_cache.valid_load_responses(responses));
                    assert(false);
                    /*
                    assert(pre_cache.lookup_map.contains_key(addr));
                    let slot = pre_cache.lookup_map[addr];
                    assert(pre_cache.entries[slot] is Loading);
                    assert(!cache_filled_addr(pre_cache, addr));
                    assert(!pre_cd.cache.contains_key(addr));
                    assert(disk.content.contains_key(addr));
                    assert(pre_cd.persistent.contains_key(addr));
                    assert(pre_cd.persistent[addr] == disk.content[addr]);
                    assert(pre_cd.readable().contains_key(addr));

                    assert(slot_addr_map.contains_key(slot)) by {
                        let restricted = pre_cache.lookup_map.restrict(responses.dom());
                        assert(restricted.contains_key(addr));
                        assert(restricted[addr] == slot);
                        Cache::State::invert_contains_pair(restricted, slot);
                    }
                    assert(slot_addr_map[slot] == addr);
                    assert(updated_entries.contains_key(slot));
                    assert(post_cache.entries[slot] == Entry::Filled{
                        addr,
                        data: responses[addr]->data,
                    });
                    assert(cache_filled_addr(post_cache, addr));
                    assert(post_cd.cache.contains_key(addr));
                    assert(post_cd.cache[addr] == responses[addr]->data);
                    assert(responses[addr]->data == disk.content[addr]);
                    assert(post_cd.readable().contains_key(addr));
                    assert(post_cd.readable()[addr] == post_cd.cache[addr]);
                    assert(pre_cd.readable()[addr] == pre_cd.persistent[addr]);
                    */
                } else {
                    if post_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(post_cache, addr));
                        assert(post_cache.lookup_map.contains_key(addr));
                        let slot = post_cache.lookup_map[addr];
                        assert(pre_cache.lookup_map.contains_key(addr));
                        assert(pre_cache.lookup_map[addr] == slot);
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(slot_addr_map.contains_key(slot));
                                let loaded_addr = slot_addr_map[slot];
                                assert(responses.contains_key(loaded_addr));
                                assert(pre_cache.lookup_map[loaded_addr] == slot) by {
                                    Cache::State::invert_contains_pair(
                                        pre_cache.lookup_map.restrict(responses.dom()),
                                        slot,
                                    );
                                }
                                assert(pre_cache.lookup_map[addr] == slot);
                                assert(loaded_addr == addr) by {
                                    assert(pre_cache.lookup_map.is_injective());
                                }
                                assert(responses.contains_key(addr));
                                assert(false);
                            }
                        }
                        assert(post_cache.entries[slot] == pre_cache.entries[slot]);
                        assert(cache_filled_addr(pre_cache, addr));
                        assert(pre_cd.cache.contains_key(addr));
                        assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                    }
                    if pre_cd.cache.contains_key(addr) {
                        assert(cache_filled_addr(pre_cache, addr));
                        cache_disk_ops_end_preserves_filled_page(
                            pre_cache,
                            post_cache,
                            responses,
                            addr,
                        );
                        assert(cache_filled_addr(post_cache, addr));
                        assert(post_cd.cache.contains_key(addr));
                        assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                    }
                    assert(post_cd.persistent.contains_key(addr)
                        == pre_cd.persistent.contains_key(addr));
                    if post_cd.persistent.contains_key(addr) {
                        assert(post_cd.persistent[addr] == pre_cd.persistent[addr]);
                    }
                }
            },
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(pre_cache, post_cache, lbl)) by {
                    reveal(Cache::State::writeback_complete);
                }
                assert(post_cache.entries == pre_cache.entries);
                assert(post_cache.lookup_map == pre_cache.lookup_map);
                if post_cd.cache.contains_key(addr) {
                    assert(cache_filled_addr(post_cache, addr));
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                }
                if pre_cd.cache.contains_key(addr) {
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(cache_filled_addr(post_cache, addr));
                    assert(post_cd.cache[addr] == pre_cd.cache[addr]);
                }
                assert(post_cd.persistent.contains_key(addr)
                    == pre_cd.persistent.contains_key(addr));
                if post_cd.persistent.contains_key(addr) {
                    assert(post_cd.persistent[addr] == pre_cd.persistent[addr]);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_disk_ops_end_preserves_filled_page(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    responses: Map<Address, DiskResponse>,
    addr: Address,
)
    requires
        pre_cache.inv(),
        cache_filled_addr(pre_cache, addr),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses},
        ),
    ensures
        cache_filled_addr(post_cache, addr),
        cache_filled_page(post_cache, addr) == cache_filled_page(pre_cache, addr),
{
    let lbl = Cache::Label::DiskOps{requests: Set::empty(), responses};
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(pre_cache, post_cache, lbl, step);
    match step {
        Cache::Step::load_complete() => {
            assert(Cache::State::load_complete(pre_cache, post_cache, lbl)) by {
                reveal(Cache::State::load_complete);
            }
            assert(!responses.contains_key(addr)) by {
                if responses.contains_key(addr) {
                    assert(pre_cache.valid_load_responses(responses));
                    assert(pre_cache.entries[pre_cache.lookup_map[addr]] is Loading);
                    assert(pre_cache.entries[pre_cache.lookup_map[addr]] is Filled);
                    assert(false);
                }
            }
            let slot_addr_map = pre_cache.lookup_map.restrict(responses.dom()).invert();
            let updated_entries = Map::new(
                |slot| slot_addr_map.contains_key(slot),
                |slot| Entry::Filled{
                    addr: slot_addr_map[slot],
                    data: responses[slot_addr_map[slot]]->data,
                },
            );
            let slot = pre_cache.lookup_map[addr];
            assert(!updated_entries.contains_key(slot)) by {
                if updated_entries.contains_key(slot) {
                    assert(slot_addr_map.contains_key(slot));
                    let response_addr = slot_addr_map[slot];
                    assert(responses.contains_key(response_addr));
                    assert(pre_cache.lookup_map[response_addr] == slot) by {
                        Cache::State::invert_contains_pair(
                            pre_cache.lookup_map.restrict(responses.dom()),
                            slot,
                        );
                    }
                    assert(pre_cache.lookup_map[addr] == slot);
                    assert(response_addr == addr) by {
                        assert(pre_cache.lookup_map.is_injective());
                    }
                    assert(responses.contains_key(addr));
                    assert(false);
                }
            }
            assert(post_cache.lookup_map == pre_cache.lookup_map);
            assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
            assert(post_cache.entries[slot] == pre_cache.entries[slot]);
            assert(cache_filled_addr(post_cache, addr));
        },
        Cache::Step::writeback_complete() => {
            assert(Cache::State::writeback_complete(pre_cache, post_cache, lbl)) by {
                reveal(Cache::State::writeback_complete);
            }
            assert(post_cache.entries == pre_cache.entries);
            assert(post_cache.lookup_map == pre_cache.lookup_map);
            assert(cache_filled_addr(post_cache, addr));
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_evictable_refines_observe_clean_aus(
    cache: Cache::State,
    disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    aus: Set<AU>,
)
    requires
        cache.inv(),
        Cache::State::next(cache, cache, Cache::Label::EvictableCheck{aus}),
    ensures
        CachingDisk::State::next(
            caching_disk_i(cache, disk, owned_aus),
            caching_disk_i(cache, disk, owned_aus),
            CachingDisk::Label::ObserveCleanAUs{aus},
        ),
{
    let cd = caching_disk_i(cache, disk, owned_aus);
    assert forall |addr: Address| #[trigger] cd.cache.contains_key(addr) && aus.contains(addr.au)
        implies {
            &&& cd.status.contains_key(addr)
            &&& cd.status[addr] == CachingDiskPageStatus::Clean
        } by {
        assert(project_cache_pages(cache, owned_aus).contains_key(addr));
        assert(cache_filled_addr(cache, addr));
        assert(cache.lookup_map.contains_key(addr));
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            cache,
            cache,
            Cache::Label::EvictableCheck{aus},
            Cache::Step::evictable(),
        ));
        reveal(Cache::State::evictable);
        assert(cache.entries[cache.lookup_map[addr]] is Filled);
        assert(cache.status_map[cache.lookup_map[addr]] is Clean);
        assert(cache.status_map[cache.lookup_map[addr]] == CacheStatus::Clean);
        assert(cache.status_map.contains_key(cache.lookup_map[addr]));
        assert(filled_cache_status(cache).contains_key(addr));
        assert(project_cache_status(cache, owned_aus).contains_key(addr));
        assert(cache_status_i(cache, addr) == CachingDiskPageStatus::Clean);
        assert(cd.status[addr] == CachingDiskPageStatus::Clean);
    }
    cd.aus_clean_or_evictable_from_forall(aus);
    assert(CachingDisk::State::next_by(
        cd,
        cd,
        CachingDisk::Label::ObserveCleanAUs{aus},
        CachingDisk::Step::observe_clean_aus(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);
}

pub proof fn ownership_projection_forget_refines(
    cache: Cache::State,
    disk: AsyncDisk::State,
    pre_owned_aus: Set<AU>,
    forgotten_aus: Set<AU>,
)
    ensures
        CachingDisk::State::next(
            caching_disk_i(cache, disk, pre_owned_aus),
            caching_disk_i(cache, disk, pre_owned_aus - forgotten_aus),
            CachingDisk::Label::Forget{aus: forgotten_aus},
        ),
{
    let pre_cd = caching_disk_i(cache, disk, pre_owned_aus);
    let post_cd = caching_disk_i(cache, disk, pre_owned_aus - forgotten_aus);
    let forgotten_addrs = addresses_in_aus(forgotten_aus);
    assert(post_cd.cache == pre_cd.cache.remove_keys(forgotten_addrs)) by {
        assert_maps_equal!(post_cd.cache, pre_cd.cache.remove_keys(forgotten_addrs), addr => {
            if post_cd.cache.contains_key(addr) {
                assert(addresses_in_aus(pre_owned_aus - forgotten_aus).contains(addr));
                assert(addresses_in_aus(pre_owned_aus).contains(addr));
                assert(!forgotten_addrs.contains(addr));
            }
            if pre_cd.cache.remove_keys(forgotten_addrs).contains_key(addr) {
                assert(pre_cd.cache.contains_key(addr));
                assert(addresses_in_aus(pre_owned_aus).contains(addr));
                assert(!forgotten_addrs.contains(addr));
                assert(!forgotten_aus.contains(addr.au));
                assert((pre_owned_aus - forgotten_aus).contains(addr.au));
                assert(addresses_in_aus(pre_owned_aus - forgotten_aus).contains(addr));
            }
        });
    }
    assert(post_cd.persistent == pre_cd.persistent.remove_keys(forgotten_addrs)) by {
        assert_maps_equal!(post_cd.persistent, pre_cd.persistent.remove_keys(forgotten_addrs), addr => {
            if post_cd.persistent.contains_key(addr) {
                assert(addresses_in_aus(pre_owned_aus - forgotten_aus).contains(addr));
                assert(addresses_in_aus(pre_owned_aus).contains(addr));
                assert(!forgotten_addrs.contains(addr));
            }
            if pre_cd.persistent.remove_keys(forgotten_addrs).contains_key(addr) {
                assert(pre_cd.persistent.contains_key(addr));
                assert(addresses_in_aus(pre_owned_aus).contains(addr));
                assert(!forgotten_addrs.contains(addr));
                assert(!forgotten_aus.contains(addr.au));
                assert((pre_owned_aus - forgotten_aus).contains(addr.au));
                assert(addresses_in_aus(pre_owned_aus - forgotten_aus).contains(addr));
            }
        });
    }
    assert(post_cd.status == pre_cd.status.remove_keys(forgotten_addrs)) by {
        assert_maps_equal!(post_cd.status, pre_cd.status.remove_keys(forgotten_addrs), addr => {
            if post_cd.status.contains_key(addr) {
                assert(addresses_in_aus(pre_owned_aus - forgotten_aus).contains(addr));
                assert(addresses_in_aus(pre_owned_aus).contains(addr));
                assert(!forgotten_addrs.contains(addr));
            }
            if pre_cd.status.remove_keys(forgotten_addrs).contains_key(addr) {
                assert(pre_cd.status.contains_key(addr));
                assert(addresses_in_aus(pre_owned_aus).contains(addr));
                assert(!forgotten_addrs.contains(addr));
                assert(!forgotten_aus.contains(addr.au));
                assert((pre_owned_aus - forgotten_aus).contains(addr.au));
                assert(addresses_in_aus(pre_owned_aus - forgotten_aus).contains(addr));
            }
        });
    }
    assert(CachingDisk::State::next_by(
        pre_cd,
        post_cd,
        CachingDisk::Label::Forget{aus: forgotten_aus},
        CachingDisk::Step::forget(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);
}

pub proof fn async_disk_process_write_refines_persist_writeback(
    cache: Cache::State,
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    id: ID,
)
    requires
        AsyncDisk::State::next_by(
            pre_disk,
            post_disk,
            AsyncDisk::Label::Internal{},
            AsyncDisk::Step::process_write(id),
        ),
        pre_disk.requests.contains_key(id),
        pre_disk.requests[id] is WriteReq,
        owned_aus.contains(pre_disk.requests[id]->to.au),
        cache_filled_addr(cache, pre_disk.requests[id]->to),
        cache_filled_page(cache, pre_disk.requests[id]->to) == pre_disk.requests[id]->data,
        filled_cache_status(cache).contains_key(pre_disk.requests[id]->to),
        filled_cache_status(cache)[pre_disk.requests[id]->to] == CachingDiskPageStatus::Writeback,
    ensures
        CachingDisk::State::next_by(
            caching_disk_i(cache, pre_disk, owned_aus),
            caching_disk_i(cache, post_disk, owned_aus),
            CachingDisk::Label::Internal{},
            CachingDisk::Step::persist_writeback(set![pre_disk.requests[id]->to]),
        ),
{
    reveal(AsyncDisk::State::next_by);
    let req = pre_disk.requests[id];
    let addr = req->to;
    let addrs = set![addr];
    let pre_cd = caching_disk_i(cache, pre_disk, owned_aus);
    let post_cd = caching_disk_i(cache, post_disk, owned_aus);
    assert(post_disk.content == pre_disk.content.insert(addr, req->data));
    assert(pre_cd.all_status(addrs, CachingDiskPageStatus::Writeback)) by {
        assert forall |a: Address| #[trigger] addrs.contains(a) implies {
            &&& pre_cd.status.contains_key(a)
            &&& pre_cd.status[a] == CachingDiskPageStatus::Writeback
        } by {
            assert(a == addr);
            assert(addresses_in_aus(owned_aus).contains(a));
            assert(project_cache_status(cache, owned_aus).contains_key(a));
        }
    }
    assert(post_cd.cache == pre_cd.cache);
    assert(post_cd.status == pre_cd.status);
    assert(post_cd.persistent == pre_cd.persistent.union_prefer_right(pre_cd.cache.restrict(addrs))) by {
        assert_maps_equal!(
            post_cd.persistent,
            pre_cd.persistent.union_prefer_right(pre_cd.cache.restrict(addrs)),
            a => {
                if a == addr {
                    assert(addresses_in_aus(owned_aus).contains(a));
                    assert(post_disk.content.contains_key(a));
                    assert(post_disk.content[a] == req->data);
                    assert(pre_cd.cache.contains_key(a));
                    assert(pre_cd.cache[a] == req->data);
                    assert(pre_cd.cache.restrict(addrs).contains_key(a));
                } else {
                    if post_cd.persistent.contains_key(a) {
                        assert(addresses_in_aus(owned_aus).contains(a));
                        assert(post_disk.content.contains_key(a));
                        assert(post_disk.content[a] == pre_disk.content[a]);
                    }
                    if pre_cd.persistent.union_prefer_right(pre_cd.cache.restrict(addrs)).contains_key(a) {
                        if pre_cd.cache.restrict(addrs).contains_key(a) {
                            assert(addrs.contains(a));
                            assert(a == addr);
                            assert(false);
                        } else {
                            assert(pre_cd.persistent.contains_key(a));
                            assert(pre_disk.content.contains_key(a));
                            assert(post_disk.content.contains_key(a));
                            assert(post_disk.content[a] == pre_disk.content[a]);
                        }
                    }
                }
            }
        );
    }
    assert(CachingDisk::State::persist_writeback(
        pre_cd,
        post_cd,
        CachingDisk::Label::Internal{},
        addrs,
    )) by {
        reveal(CachingDisk::State::persist_writeback);
    }
    assert(CachingDisk::State::next_by(
        pre_cd,
        post_cd,
        CachingDisk::Label::Internal{},
        CachingDisk::Step::persist_writeback(addrs),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
}

pub proof fn async_disk_process_write_refines_projected_internal(
    cache: Cache::State,
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    id: ID,
)
    requires
        AsyncDisk::State::next_by(
            pre_disk,
            post_disk,
            AsyncDisk::Label::Internal{},
            AsyncDisk::Step::process_write(id),
        ),
        pre_disk.requests.contains_key(id),
        pre_disk.requests[id] is WriteReq,
        owned_aus.contains(pre_disk.requests[id]->to.au) ==> {
            &&& cache_filled_addr(cache, pre_disk.requests[id]->to)
            &&& cache_filled_page(cache, pre_disk.requests[id]->to) == pre_disk.requests[id]->data
            &&& filled_cache_status(cache).contains_key(pre_disk.requests[id]->to)
            &&& filled_cache_status(cache)[pre_disk.requests[id]->to]
                == CachingDiskPageStatus::Writeback
        },
    ensures
        CachingDisk::State::next(
            caching_disk_i(cache, pre_disk, owned_aus),
            caching_disk_i(cache, post_disk, owned_aus),
            CachingDisk::Label::Internal{},
        ),
{
    reveal(AsyncDisk::State::next_by);
    let req = pre_disk.requests[id];
    let addr = req->to;
    assert(post_disk.content == pre_disk.content.insert(addr, req->data));
    if owned_aus.contains(addr.au) {
        async_disk_process_write_refines_persist_writeback(
            cache,
            pre_disk,
            post_disk,
            owned_aus,
            id,
        );
        assert(CachingDisk::State::next_by(
            caching_disk_i(cache, pre_disk, owned_aus),
            caching_disk_i(cache, post_disk, owned_aus),
            CachingDisk::Label::Internal{},
            CachingDisk::Step::persist_writeback(set![addr]),
        ));
        reveal(CachingDisk::State::next);
    } else {
        let pre_cd = caching_disk_i(cache, pre_disk, owned_aus);
        let post_cd = caching_disk_i(cache, post_disk, owned_aus);
        assert(post_cd.cache == pre_cd.cache);
        assert(post_cd.status == pre_cd.status);
        assert(post_cd.persistent == pre_cd.persistent) by {
            assert_maps_equal!(
                post_cd.persistent,
                pre_cd.persistent,
                a => {
                    if post_cd.persistent.contains_key(a) {
                        assert(addresses_in_aus(owned_aus).contains(a));
                        assert(owned_aus.contains(a.au));
                        assert(a != addr);
                        assert(post_disk.content[a] == pre_disk.content[a]);
                    }
                    if pre_cd.persistent.contains_key(a) {
                        assert(addresses_in_aus(owned_aus).contains(a));
                        assert(owned_aus.contains(a.au));
                        assert(a != addr);
                        assert(post_disk.content[a] == pre_disk.content[a]);
                    }
                }
            );
        }
        assert(post_cd == pre_cd);
        assert(pre_cd.all_status(Set::<Address>::empty(), CachingDiskPageStatus::Writeback));
        assert(pre_cd.cache.restrict(Set::<Address>::empty()) == Map::<Address, RawPage>::empty()) by {
            assert_maps_equal!(
                pre_cd.cache.restrict(Set::<Address>::empty()),
                Map::<Address, RawPage>::empty(),
                a => {
                    if pre_cd.cache.restrict(Set::<Address>::empty()).contains_key(a) {
                        assert(false);
                    }
                }
            );
        }
        assert(pre_cd.persistent.union_prefer_right(
            pre_cd.cache.restrict(Set::<Address>::empty()),
        ) == pre_cd.persistent) by {
            assert_maps_equal!(
                pre_cd.persistent.union_prefer_right(
                    pre_cd.cache.restrict(Set::<Address>::empty()),
                ),
                pre_cd.persistent,
                a => {}
            );
        }
        assert(CachingDisk::State::persist_writeback(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
            Set::<Address>::empty(),
        )) by {
            reveal(CachingDisk::State::persist_writeback);
        }
        assert(CachingDisk::State::next_by(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
            CachingDisk::Step::persist_writeback(Set::<Address>::empty()),
        )) by {
            reveal(CachingDisk::State::next_by);
        }
        reveal(CachingDisk::State::next);
    }
}

pub proof fn async_disk_process_write_preserves_readable(
    cache: Cache::State,
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
    owned_aus: Set<AU>,
    id: ID,
)
    requires
        AsyncDisk::State::next_by(
            pre_disk,
            post_disk,
            AsyncDisk::Label::Internal{},
            AsyncDisk::Step::process_write(id),
        ),
        pre_disk.requests.contains_key(id),
        pre_disk.requests[id] is WriteReq,
        owned_aus.contains(pre_disk.requests[id]->to.au) ==> {
            &&& cache_filled_addr(cache, pre_disk.requests[id]->to)
            &&& cache_filled_page(cache, pre_disk.requests[id]->to) == pre_disk.requests[id]->data
            &&& filled_cache_status(cache).contains_key(pre_disk.requests[id]->to)
            &&& filled_cache_status(cache)[pre_disk.requests[id]->to]
                == CachingDiskPageStatus::Writeback
        },
    ensures
        caching_disk_i(cache, post_disk, owned_aus).readable()
            == caching_disk_i(cache, pre_disk, owned_aus).readable(),
{
    reveal(AsyncDisk::State::next_by);
    let req = pre_disk.requests[id];
    let addr = req->to;
    let pre_cd = caching_disk_i(cache, pre_disk, owned_aus);
    let post_cd = caching_disk_i(cache, post_disk, owned_aus);
    assert(post_disk.content == pre_disk.content.insert(addr, req->data));
    if owned_aus.contains(addr.au) {
        async_disk_process_write_refines_persist_writeback(
            cache,
            pre_disk,
            post_disk,
            owned_aus,
            id,
        );
        assert(CachingDisk::State::next_by(
            pre_cd,
            post_cd,
            CachingDisk::Label::Internal{},
            CachingDisk::Step::persist_writeback(set![addr]),
        ));
        CachingDisk::State::persist_writeback_effect(pre_cd, post_cd, set![addr]);
        assert(pre_cd.cache.contains_key(addr));
        assert(pre_cd.cache[addr] == req->data);
        assert(post_cd.cache == pre_cd.cache);
        assert(post_cd.status == pre_cd.status);
        assert(post_cd.persistent == pre_cd.persistent.union_prefer_right(
            pre_cd.cache.restrict(set![addr]),
        ));
        assert_maps_equal!(post_cd.readable(), pre_cd.readable(), a => {
            if post_cd.readable().contains_key(a) {
                if post_cd.cache.contains_key(a) {
                    assert(pre_cd.cache.contains_key(a));
                    assert(post_cd.cache[a] == pre_cd.cache[a]);
                    assert(pre_cd.readable().contains_key(a));
                    assert(post_cd.readable()[a] == post_cd.cache[a]);
                    assert(pre_cd.readable()[a] == pre_cd.cache[a]);
                } else {
                    assert(!pre_cd.cache.contains_key(a));
                    assert(post_cd.persistent.contains_key(a));
                    if pre_cd.cache.restrict(set![addr]).contains_key(a) {
                        assert(a == addr);
                        assert(pre_cd.cache.contains_key(a));
                        assert(false);
                    } else {
                        assert(pre_cd.persistent.contains_key(a));
                        assert(pre_cd.readable().contains_key(a));
                        assert(post_cd.readable()[a] == post_cd.persistent[a]);
                        assert(pre_cd.readable()[a] == pre_cd.persistent[a]);
                        assert(post_cd.persistent[a] == pre_cd.persistent[a]);
                    }
                }
            }
            if pre_cd.readable().contains_key(a) {
                if pre_cd.cache.contains_key(a) {
                    assert(post_cd.cache.contains_key(a));
                    assert(post_cd.cache[a] == pre_cd.cache[a]);
                    assert(post_cd.readable().contains_key(a));
                } else {
                    assert(pre_cd.persistent.contains_key(a));
                    assert(post_cd.persistent.contains_key(a));
                    assert(post_cd.readable().contains_key(a));
                }
            }
        });
    } else {
        assert(post_cd.cache == pre_cd.cache);
        assert(post_cd.status == pre_cd.status);
        assert(post_cd.persistent == pre_cd.persistent) by {
            assert_maps_equal!(
                post_cd.persistent,
                pre_cd.persistent,
                a => {
                    if post_cd.persistent.contains_key(a) {
                        assert(addresses_in_aus(owned_aus).contains(a));
                        assert(owned_aus.contains(a.au));
                        assert(a != addr);
                        assert(post_disk.content[a] == pre_disk.content[a]);
                    }
                    if pre_cd.persistent.contains_key(a) {
                        assert(addresses_in_aus(owned_aus).contains(a));
                        assert(owned_aus.contains(a.au));
                        assert(a != addr);
                        assert(post_disk.content[a] == pre_disk.content[a]);
                    }
                }
            );
        }
        assert(post_cd == pre_cd);
    }
}

} // verus!
