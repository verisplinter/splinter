// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::disk::GenericDisk_v::Address;
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, IRawPage, PAGE_SIZE_BYTES,
};
use crate::implementation::CachingDiskBranchBetree_v::to_betree_nodes;
use crate::implementation::CachedBranchBetree_v::LoadedBetree;
use crate::marshalling::IBetreeNodeFormat_v::raw_page_to_betree_node;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::IAddress;

verus! {

pub struct BetreeWriteEntry {
    pub addr: IAddress,
    pub page: IRawPage,
}

impl BetreeWriteEntry {
    pub open spec fn wf(&self) -> bool {
        &&& self.addr@.wf()
        &&& self.page@.len() == PAGE_SIZE_BYTES
    }
}

pub open spec fn betree_write_addrs_unique(
    entries: Seq<BetreeWriteEntry>,
) -> bool {
    forall |i: int, j: int|
        #![trigger entries[i].addr, entries[j].addr]
        0 <= i < entries.len()
        && 0 <= j < entries.len()
        && entries[i].addr == entries[j].addr
        ==> i == j
}

pub open spec fn betree_write_entries_wf(
    entries: Seq<BetreeWriteEntry>,
) -> bool {
    &&& betree_write_addrs_unique(entries)
    &&& forall |i: int| 0 <= i < entries.len()
        ==> (#[trigger] entries[i]).wf()
}

pub open spec fn betree_raw_writes(
    entries: Seq<BetreeWriteEntry>,
) -> Map<Address, RawPage>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Map::empty()
    } else {
        betree_raw_writes(entries.drop_last()).insert(
            entries.last().addr@,
            entries.last().page@,
        )
    }
}

pub open spec fn betree_node_writes(
    entries: Seq<BetreeWriteEntry>,
) -> LoadedBetree
    decreases entries.len(),
{
    if entries.len() == 0 {
        Map::empty()
    } else {
        betree_node_writes(entries.drop_last()).insert(
            entries.last().addr@,
            raw_page_to_betree_node(entries.last().page@),
        )
    }
}

pub proof fn betree_raw_writes_to_nodes(
    entries: Seq<BetreeWriteEntry>,
)
    ensures
        to_betree_nodes(betree_raw_writes(entries))
            == betree_node_writes(entries),
    decreases entries.len(),
{
    if entries.len() > 0 {
        betree_raw_writes_to_nodes(entries.drop_last());
        assert_maps_equal!(
            to_betree_nodes(betree_raw_writes(entries)),
            betree_node_writes(entries),
            addr => {}
        );
    } else {
        assert(to_betree_nodes(betree_raw_writes(entries)).is_empty());
    }
}

pub proof fn betree_node_writes_push(
    entries: Seq<BetreeWriteEntry>,
    entry: BetreeWriteEntry,
)
    ensures
        betree_node_writes(entries.push(entry))
            == betree_node_writes(entries).insert(
                entry.addr@,
                raw_page_to_betree_node(entry.page@),
            ),
{

    assert(entries.push(entry).drop_last() == entries);
    assert(entries.push(entry).last() == entry);
}

pub proof fn betree_raw_writes_dom(
    entries: Seq<BetreeWriteEntry>,
)
    ensures
        betree_raw_writes(entries).dom()
            =~= Set::new(|addr: Address| exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].addr@ == addr),
    decreases entries.len(),
{
    if entries.len() > 0 {
        betree_raw_writes_dom(entries.drop_last());
        let prefix = entries.drop_last();
        let last = entries.last();
        assert(entries == prefix.push(last));
        assert forall |addr: Address|
            #![trigger betree_raw_writes(entries).dom().contains(addr)]
            betree_raw_writes(entries).dom().contains(addr)
            == Set::new(|candidate: Address| exists |i: int| #![auto]
                0 <= i < entries.len()
                && entries[i].addr@ == candidate).contains(addr) by {
            if addr == last.addr@ {
                assert(entries[entries.len() - 1].addr@ == addr);
            } else if exists |i: int| #![auto]
                0 <= i < entries.len() && entries[i].addr@ == addr
            {
                let i = choose |i: int| #![auto]
                    0 <= i < entries.len() && entries[i].addr@ == addr;
                assert(i < prefix.len());
                assert(prefix[i] == entries[i]);
            }
        }
    } else {
        assert(betree_raw_writes(entries).dom().is_empty());
    }
}

pub proof fn betree_write_entries_push(
    entries: Seq<BetreeWriteEntry>,
    entry: BetreeWriteEntry,
)
    requires
        betree_write_entries_wf(entries),
        entry.wf(),
        !betree_raw_writes(entries).dom().contains(entry.addr@),
    ensures betree_write_entries_wf(entries.push(entry)),
{
    betree_raw_writes_dom(entries);
    assert forall |i: int, j: int|
        #![trigger entries.push(entry)[i].addr,
            entries.push(entry)[j].addr]
        0 <= i < entries.push(entry).len()
        && 0 <= j < entries.push(entry).len()
        && entries.push(entry)[i].addr == entries.push(entry)[j].addr
        implies i == j by {
        if i < entries.len() && j < entries.len() {
            assert(entries.push(entry)[i] == entries[i]);
            assert(entries.push(entry)[j] == entries[j]);
        } else if i < entries.len() {
            assert(j == entries.len());
            assert(entries.push(entry)[j] == entry);
            assert(betree_raw_writes(entries).dom()
                .contains(entries[i].addr@));
        } else if j < entries.len() {
            assert(i == entries.len());
            assert(entries.push(entry)[i] == entry);
            assert(betree_raw_writes(entries).dom()
                .contains(entries[j].addr@));
        }
    }
    assert forall |i: int| 0 <= i < entries.push(entry).len()
        implies (#[trigger] entries.push(entry)[i]).wf() by {
        if i == entries.len() {
            assert(entries.push(entry)[i] == entry);
        } else {
            assert(entries.push(entry)[i] == entries[i]);
        }
    }
}

proof fn write_prefix_preserves_available(
    before: FracCacheImpl,
    after: FracCacheImpl,
    written_addr: IAddress,
    written_slot: usize,
    candidate: IAddress,
)
    requires
        before.wf(),
        after.wf(),
        before.entry_available_for_fetch(&candidate),
        candidate != written_addr,
        after.entry_fetched(&written_addr),
        after.lookup_addr_slot(&written_addr) == written_slot,
        after.entry_fetched_same_except(before, &written_addr),
        after.entries_same_except(before, written_slot),
    ensures after.entry_available_for_fetch(&candidate),
{
    FracCacheImpl::entry_available_preserved_except(
        before,
        after,
        &written_addr,
        written_slot,
        &candidate,
    );
}

pub fn write_betree_pages(
    cache: &mut FracCacheImpl,
    entries_in: Vec<BetreeWriteEntry>,
)
    requires
        old(cache).wf(),
        old(cache)@.inv(),
        betree_write_entries_wf(entries_in@),
        forall |i: int| 0 <= i < entries_in@.len()
            ==> old(cache).entry_available_for_fetch(
                &(#[trigger] entries_in@[i]).addr,
            ),
    ensures
        cache.wf(),
        cache@.inv(),
        cache.valid_load_handles_preserved(*old(cache)),
        Cache::State::next(
            old(cache)@,
            cache@,
            Cache::Label::Access {
                reads: Map::empty(),
                writes: betree_raw_writes(entries_in@),
            },
        ),
        forall |candidate: IAddress|
            old(cache).entry_available_for_fetch(&candidate)
            && !betree_raw_writes(entries_in@).dom().contains(candidate@)
            ==> cache.entry_available_for_fetch(&candidate),
    decreases entries_in.len(),
{
    let ghost input_view = entries_in@;
    let mut entries = entries_in;
    if entries.len() == 0 {
        proof {
            assert(betree_raw_writes(input_view).is_empty());
            Cache::State::access_empty_is_noop(cache@);
            assert(cache.valid_load_handles_preserved(*cache));
        }
        return;
    }

    let ghost original_entries = entries@;
    let ghost cache0 = *cache;
    let entry = entries.pop().unwrap();
    let ghost prefix_entries = entries@;
    proof {
        assert(original_entries == prefix_entries.push(entry));
        assert(betree_write_entries_wf(prefix_entries)) by {
            assert(betree_write_addrs_unique(prefix_entries));
        }
        assert forall |i: int| 0 <= i < prefix_entries.len()
            implies cache0.entry_available_for_fetch(
                &(#[trigger] prefix_entries[i]).addr,
            ) by {
            assert(prefix_entries[i] == original_entries[i]);
        }
    }
    write_betree_pages(cache, entries);
    let ghost after_prefix = *cache;
    proof {
        betree_raw_writes_dom(prefix_entries);
        assert(!betree_raw_writes(prefix_entries).dom()
            .contains(entry.addr@)) by {
            if betree_raw_writes(prefix_entries).dom().contains(entry.addr@) {
                let i = choose |i: int| #![auto]
                    0 <= i < prefix_entries.len()
                    && prefix_entries[i].addr == entry.addr;
                assert(original_entries[i].addr
                    == original_entries[original_entries.len() - 1].addr);
                assert(i != original_entries.len() - 1);
            }
        }
        assert(cache0.entry_available_for_fetch(&entry.addr));
        assert(after_prefix.entry_available_for_fetch(&entry.addr));
    }

    let ghost before_fetch = *cache;
    let mut handle = match cache.fetch(&entry.addr, false) {
        FetchErrorCode::Success { slot_handle } => slot_handle,
        _ => {
            proof {
                assert(before_fetch.entry_available_for_fetch(&entry.addr));
                assert(false);
            }
            return;
        },
    };
    let slot = handle.idx;
    let ghost borrowed = *cache;
    proof {
        FracCacheImpl::valid_write_handle_model_entry(
            &borrowed,
            &entry.addr,
            handle,
        );
    }
    let ghost page = entry.page@;
    handle.rec = entry.page;
    cache.write_release(&entry.addr, handle);
    let ghost singleton = map![entry.addr@ => page];
    proof {
        assert(before_fetch@.valid_write(entry.addr@));
        assert(borrowed@.lookup_map == before_fetch@.lookup_map);
        assert(borrowed@.status_map == before_fetch@.status_map);
        assert(before_fetch@.lookup_map.contains_key(entry.addr@));
        assert(before_fetch@.lookup_map[entry.addr@] == slot);
        assert(before_fetch@.entries
            == borrowed@.entries.insert(
                slot,
                before_fetch@.entries[slot],
            ));
        Cache::State::access_from_borrowed_write_slot(
            before_fetch@,
            borrowed@,
            cache@,
            Map::empty(),
            entry.addr@,
            slot,
            page,
        );
        assert(betree_raw_writes(prefix_entries).dom()
            .disjoint(singleton.dom()));
        Cache::State::access_compose_disjoint_writes(
            cache0@,
            after_prefix@,
            cache@,
            betree_raw_writes(prefix_entries),
            singleton,
        );
        assert(betree_raw_writes(original_entries)
            == betree_raw_writes(prefix_entries)
                .union_prefer_right(singleton));
        Cache::State::inv_next(
            cache0@,
            cache@,
            Cache::Label::Access {
                reads: Map::empty(),
                writes: betree_raw_writes(original_entries),
            },
        );
        FracCacheImpl::valid_load_handles_preserved_transitive(
            cache0,
            after_prefix,
            borrowed,
        );
        FracCacheImpl::valid_load_handles_preserved_transitive(
            cache0,
            borrowed,
            *cache,
        );

        assert forall |candidate: IAddress|
            cache0.entry_available_for_fetch(&candidate)
            && !betree_raw_writes(original_entries).dom().contains(candidate@)
            implies cache.entry_available_for_fetch(&candidate) by {
            assert(!betree_raw_writes(prefix_entries).dom()
                .contains(candidate@));
            assert(after_prefix.entry_available_for_fetch(&candidate));
            assert(candidate != entry.addr);
            FracCacheImpl::entry_available_preserved_except(
                before_fetch,
                borrowed,
                &entry.addr,
                slot,
                &candidate,
            );
            write_prefix_preserves_available(
                borrowed,
                *cache,
                entry.addr,
                slot,
                candidate,
            );
        }
    }
}

} // verus!
