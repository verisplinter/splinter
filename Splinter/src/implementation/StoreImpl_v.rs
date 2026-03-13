// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::spec::AsyncDisk_t::{Address, RawPage};
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::TotalKMMap_t::TotalKMMap;
use crate::implementation::FracCacheImpl_v::{FetchErrorCode, FracCacheImpl, MutHandle, PAGE_SIZE_BYTES, cache_load_label};
use crate::implementation::Cache_v::Cache;
use crate::implementation::PageAllocator_v::PageAllocator;
use crate::implementation::JournalImpl_v::iaddr_view;
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::implementation::SuperblockTypes_v;
use crate::implementation::VecMap_v::VecMap;
use crate::marshalling::IStoreFormat_v;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;

verus! {

pub closed spec(checked) fn view_as_kmmap(store: VecMap<Key, Value>) -> TotalKMMap
{
    SuperblockTypes_v::map_to_kmmap(store@)
}

pub proof fn view_as_kmmap_empty(store: VecMap<Key, Value>)
requires
    store.wf(),
    store@.is_empty(),
ensures
    view_as_kmmap(store) == TotalKMMap::empty(),
{
    let lhs = view_as_kmmap(store);
    assert(lhs.ext_equal(TotalKMMap::empty())) by {
        assert forall |k: Key| #[trigger] lhs.0[k] == TotalKMMap::empty().0[k] by {
            assert(!store@.contains_key(k));
        }
    };
    lhs.ext_equal_is_equality(TotalKMMap::empty());
}

pub open spec fn raw_page_to_store_kmmap(raw_page: RawPage) -> TotalKMMap
{
    let fmt = IStoreFormat_v::spec_new();
    if fmt.parsable(raw_page) {
        SuperblockTypes_v::map_to_kmmap(VecMap::<Key, Value>::seq_to_map(fmt.parse(raw_page)))
    } else {
        arbitrary()
    }
}

pub enum LoadMapResult {
    LoadInitiate{slot_handle: MutHandle},
    LoadComplete{reads: Ghost<Map<Address, RawPage>>},
    LoadInProgress{},
}

pub struct StoreImpl {
    store: VecMap<Key, Value>,
    store_lsn: u64,
    persistent_store_ptr: Option<IAddress>,
    prepared_store_ptr: Option<IAddress>,
    prepared_store_lsn: u64,
    store_alloc: PageAllocator,
}

impl StoreImpl {
    #[verifier::external_body]
    fn todo_placeholder()
        ensures false
    {
        panic!();
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.store.wf()
        &&& self.kmmap().wf()
        &&& self.store_alloc.wf()
        &&& self.persistent_store_ptr is Some
            ==> (self.persistent_store_ptr.unwrap().page as nat) < self.next_alloc_page()
        &&& self.prepared_store_ptr is Some
            ==> self.prepared_store_ptr.unwrap().au as nat == self.alloc_au() as nat
        &&& self.prepared_store_ptr is Some
            ==> (self.prepared_store_ptr.unwrap().page as nat) < self.next_alloc_page()
    }

    pub fn new(init_store_ptr: Option<IAddress>, alloc_au: u32) -> (out: Self)
        ensures
            out.wf(),
            out.alloc_au() == alloc_au,
            out.persistent_store_ptr() == init_store_ptr,
            out.persistent_store_ptr_view() == iaddr_view(init_store_ptr),
            out.prepared_store_ptr() is None,
            out.prepared_store_ptr_view() is None,
            out.prepared_store_lsn() == 0,
            out.prepared_store_lsn_nat() == 0,
    {
        let start_page = match init_store_ptr {
            Some(ptr) => {
                if ptr.page == u32::MAX {
                    convert_overflow_into_liveness_failure();
                }
                ptr.page + 1
            }
            None => 0,
        };
        Self {
            store: VecMap::new(),
            store_lsn: 0,
            persistent_store_ptr: init_store_ptr,
            prepared_store_ptr: None,
            prepared_store_lsn: 0,
            store_alloc: PageAllocator::new(alloc_au, start_page),
        }
    }

    pub closed spec fn alloc_au(self) -> u32 {
        self.store_alloc.alloc_au()
    }

    pub closed spec fn alloc_au_nat(self) -> nat {
        self.store_alloc.alloc_au_nat()
    }

    pub fn exec_alloc_au(&self) -> (out: u32)
        ensures out == self.alloc_au()
    {
        self.store_alloc.exec_alloc_au()
    }

    pub closed spec fn next_alloc_addr(self) -> IAddress {
        IAddress{ au: self.alloc_au(), page: self.store_alloc.next_page() }
    }

    pub closed spec fn next_alloc_page(self) -> nat {
        self.store_alloc.next_page() as nat
    }

    pub closed spec fn store_entries(self) -> Map<Key, Value> {
        self.store@
    }

    pub closed spec fn store_wf(self) -> bool {
        self.store.wf()
    }

    pub closed spec fn store_lsn(self) -> u64 {
        self.store_lsn
    }

    pub closed spec fn store_lsn_nat(self) -> nat {
        self.store_lsn as nat
    }

    pub fn exec_store_lsn(&self) -> (out: u64)
        ensures
            out == self.store_lsn(),
            out as nat == self.store_lsn_nat(),
    {
        self.store_lsn
    }

    pub fn peek_next_addr(&self) -> (out: IAddress)
        requires self.wf()
        ensures
            out == self.next_alloc_addr(),
            out.au == self.alloc_au(),
            out.page as nat == self.next_alloc_page(),
    {
        self.store_alloc.peek_next_addr()
    }

    pub fn advance_next_addr(&mut self)
        requires old(self).wf()
        ensures
            self.wf(),
            self@ == old(self)@,
            self.store_lsn() == old(self).store_lsn(),
            self.store_lsn_nat() == old(self).store_lsn_nat(),
            self.persistent_store_ptr() == old(self).persistent_store_ptr(),
            self.prepared_store_ptr() == old(self).prepared_store_ptr(),
            self.prepared_store_lsn() == old(self).prepared_store_lsn(),
            self.prepared_store_lsn_nat() == old(self).prepared_store_lsn_nat(),
            self.alloc_au() == old(self).alloc_au(),
            self.next_alloc_page() == old(self).next_alloc_page() + 1,
    {
        self.store_alloc.advance_next_addr();
    }

    pub fn marshall_current_store_page(&self) -> (out: Vec<u8>)
        requires
            self.wf(),
        ensures
            out.len() == PAGE_SIZE_BYTES,
            raw_page_to_store_kmmap(out@) == self.kmmap(),
    {
        let fmt = IStoreFormat_v::new();
        let values = self.store.borrow_vec();
        if values.len() > fmt.max_length || values.len() > u8::MAX as usize {
            Self::todo_placeholder();
            return unreached();
        }
        if !VecMap::<Key, Value>::exec_unique_keys(values) {
            Self::todo_placeholder();
            return unreached();
        }
        let mut out = vec![0u8; PAGE_SIZE_BYTES];
        proof {
            assert(forall |i: int| 0 <= i < values.len() ==> fmt.marshallable_at(values@, i));
            assert(values.len() <= fmt.max_length);
            assert(values.len() <= u8::MAX as usize);
            assert(fmt.marshallable(values.parsedv()));
        }
        let end = fmt.exec_marshall(values, &mut out, 0);
        if end != PAGE_SIZE_BYTES {
            Self::todo_placeholder();
            return unreached();
        }
        proof {
            assert(out@.subrange(0, end as int) == out@);
            assert(values@ == self.store.as_seq());
            assert(VecMap::<Key, Value>::unique_keys(values@));
            VecMap::<Key, Value>::seq_to_map_ensures(values@);
            let ghost parsed_map = VecMap::<Key, Value>::seq_to_map(values@);
            let ghost lhs = raw_page_to_store_kmmap(out@);
            let ghost rhs = SuperblockTypes_v::map_to_kmmap(parsed_map);
            assert(fmt.parsable(out@));
            assert(fmt.parse(out@) == values.parsedv());
            assert(values.parsedv() == values@);
            assert(parsed_map == self.store@);
            assert(lhs.ext_equal(rhs)) by {
                let ghost lhs_map = SuperblockTypes_v::map_to_kmmap(parsed_map);
                let ghost rhs_map = SuperblockTypes_v::map_to_kmmap(self.store@);
                assert(lhs == SuperblockTypes_v::map_to_kmmap(VecMap::<Key, Value>::seq_to_map(fmt.parse(out@))));
                assert(VecMap::<Key, Value>::seq_to_map(fmt.parse(out@)) == parsed_map);
                assert(lhs == lhs_map);
                assert(rhs == rhs_map);
                assert_maps_equal!(lhs_map.0, rhs_map.0, k => {
                    if self.store@.contains_key(k) {
                        assert(parsed_map.contains_key(k));
                        assert(lhs_map.0[k] == Message::Define{value: parsed_map[k]});
                        assert(rhs_map.0[k] == Message::Define{value: self.store@[k]});
                    } else {
                        assert(!parsed_map.contains_key(k));
                        assert(lhs_map.0[k] == Message::empty());
                        assert(rhs_map.0[k] == Message::empty());
                    }
                });
            };
            lhs.ext_equal_is_equality(rhs);
        }
        out
    }

    pub fn insert(&mut self, key: Key, value: Value)
        requires
            old(self).wf(),
            old(self).persistent_store_ptr_matches_alloc_au(),
        ensures
            self.wf(),
            self.persistent_store_ptr_matches_alloc_au(),
            self.store_entries() == old(self).store_entries().insert(key, value),
            self.store_lsn() == old(self).store_lsn() + 1,
            self.store_lsn_nat() == old(self).store_lsn_nat() + 1,
            self.kmmap() == old(self).kmmap().insert(key, Message::Define{value}),
            self@ == self.kmmap(),
            self.persistent_store_ptr() == old(self).persistent_store_ptr(),
            self.persistent_store_ptr_view() == old(self).persistent_store_ptr_view(),
            self.prepared_store_ptr() == old(self).prepared_store_ptr(),
            self.prepared_store_ptr_view() == old(self).prepared_store_ptr_view(),
            self.prepared_store_lsn() == old(self).prepared_store_lsn(),
            self.prepared_store_lsn_nat() == old(self).prepared_store_lsn_nat(),
            self.alloc_au() == old(self).alloc_au(),
            self.next_alloc_page() == old(self).next_alloc_page(),
    {
        if self.store_lsn == u64::MAX {
            convert_overflow_into_liveness_failure();
        }
        self.store.insert(key, value);
        self.store_lsn = self.store_lsn + 1;
        proof {
            assert(self.persistent_store_ptr_matches_alloc_au());
        }
    }

    pub proof fn kmmap_wf_ensures(self)
        requires self.wf()
        ensures self.kmmap().wf()
    {
    }

    pub fn load_map_step(&mut self, cache: &mut FracCacheImpl, boundary_lsn: u64) -> (out: LoadMapResult)
        requires
            old(self).wf(),
            old(self).persistent_store_ptr_matches_alloc_au(),
            old(cache).wf(),
            boundary_lsn as nat <= u64::MAX,
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            self.persistent_store_ptr_view() == old(self).persistent_store_ptr_view(),
            self.persistent_store_ptr_matches_alloc_au(),
            self.prepared_store_ptr() == old(self).prepared_store_ptr(),
            self.prepared_store_ptr_view() == old(self).prepared_store_ptr_view(),
            self.prepared_store_lsn() == old(self).prepared_store_lsn(),
            self.prepared_store_lsn_nat() == old(self).prepared_store_lsn_nat(),
            self.alloc_au() == old(self).alloc_au(),
            self.next_alloc_page() == old(self).next_alloc_page(),
            match out {
                LoadMapResult::LoadInitiate{slot_handle} => {
                    &&& self.persistent_store_ptr() is Some
                    &&& !old(cache).entry_fetched(&self.persistent_store_ptr().unwrap())
                    &&& cache.entry_fetched(&self.persistent_store_ptr().unwrap())
                    &&& cache.valid_load_handle(&self.persistent_store_ptr().unwrap(), slot_handle)
                    &&& Cache::State::next(old(cache)@, cache@, cache_load_label(&self.persistent_store_ptr().unwrap()))
                },
                LoadMapResult::LoadComplete{reads} => {
                    &&& self.store_lsn_nat() == boundary_lsn as nat
                    &&& if old(self).persistent_store_ptr_view() is None {
                        &&& reads@ == Map::<Address, RawPage>::empty()
                        &&& self.kmmap() == TotalKMMap::empty()
                        &&& cache@ == old(cache)@
                    } else {
                        let ptr = old(self).persistent_store_ptr_view().unwrap();
                        &&& reads@.contains_key(ptr)
                        &&& reads@.dom() == set!{ptr}
                        &&& self.kmmap() == raw_page_to_store_kmmap(reads@[ptr])
                        &&& Cache::State::next(old(cache)@, cache@, Cache::Label::Access{reads: reads@, writes: Map::empty()})
                    }
                },
                LoadMapResult::LoadInProgress{} => {
                    &&& cache@ == old(cache)@
                },
            }
    {
        match self.persistent_store_ptr {
            None => {
                self.store = VecMap::new();
                self.store_lsn = boundary_lsn;
                let ghost reads = Map::<Address, RawPage>::empty();
                proof {
                    view_as_kmmap_empty(self.store);
                }
                LoadMapResult::LoadComplete{reads: Ghost(reads)}
            }
            Some(ptr) => {
                let ghost cache_pre_impl = *cache;
                let ghost cache_pre = cache@;
                match cache.fetch(&ptr, true) {
                    FetchErrorCode::LoadInitiate{slot_handle} => {
                        LoadMapResult::LoadInitiate{slot_handle}
                    }
                    FetchErrorCode::Awaiting => {
                        LoadMapResult::LoadInProgress{}
                    }
                    FetchErrorCode::Success{slot_handle} => {
                        let fmt = IStoreFormat_v::new();
                        let all_slice = Slice::all(&slot_handle.rec);
                        let parsable = fmt.exec_parsable(&all_slice, &slot_handle.rec);
                        if !parsable {
                            Self::todo_placeholder();
                            unreached()
                        }
                        assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                        let parsed = fmt.exec_parse(&all_slice, &slot_handle.rec);
                        let ghost raw_page = slot_handle.rec@;
                        if !VecMap::<Key, Value>::exec_unique_keys(&parsed) {
                            Self::todo_placeholder();
                            unreached()
                        }
                        let ghost cache_after_fetch_impl = *cache;
                        self.store = VecMap::from_vec(parsed);
                        self.store_lsn = boundary_lsn;
                        cache.handle_release(&ptr, slot_handle);
                        let ghost reads = map!{ptr@ => raw_page};
                        proof {
                            FracCacheImpl::valid_load_handles_preserved_transitive(
                                cache_pre_impl,
                                cache_after_fetch_impl,
                                *cache,
                            );

                            let lhs = raw_page_to_store_kmmap(raw_page);
                            let rhs = self.kmmap();
                            assert(lhs.ext_equal(rhs)) by {
                                let ghost parsed_map = VecMap::<Key, Value>::seq_to_map(parsed@);
                                let ghost lhs_map = SuperblockTypes_v::map_to_kmmap(parsed_map);
                                let ghost rhs_map = SuperblockTypes_v::map_to_kmmap(self.store@);
                                assert(fmt.parsable(raw_page));
                                assert(parsed@ == fmt.parse(raw_page));
                                assert(self.store@ == parsed_map);
                                assert(lhs == lhs_map);
                                assert(rhs == rhs_map);
                                assert_maps_equal!(lhs_map.0, rhs_map.0, k => {
                                    if self.store@.contains_key(k) {
                                        assert(parsed_map.contains_key(k));
                                        assert(lhs_map.0[k] == Message::Define{value: parsed_map[k]});
                                        assert(rhs_map.0[k] == Message::Define{value: self.store@[k]});
                                    } else {
                                        assert(!parsed_map.contains_key(k));
                                        assert(lhs_map.0[k] == Message::empty());
                                        assert(rhs_map.0[k] == Message::empty());
                                    }
                                });
                            };
                            lhs.ext_equal_is_equality(rhs);

                            let ghost cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
                            assert(cache_pre.valid_read(ptr@, raw_page));
                            assert forall |a| #[trigger] cache_lbl->reads.contains_key(a)
                                implies cache_pre.valid_read(a, cache_lbl->reads[a]) by {
                                assert(a == ptr@);
                            };
                            assert(forall |a| #[trigger] cache_lbl->writes.contains_key(a)
                                ==> cache_pre.valid_write(a));

                            let updated_entries = cache_pre.write_updated_entries(cache_lbl->writes);
                            let updated_status_map = cache_pre.write_updated_status(cache_lbl->writes);
                            assert(cache_pre.entries.union_prefer_right(updated_entries) =~= cache_pre.entries);
                            assert(cache_pre.status_map.union_prefer_right(updated_status_map) =~= cache_pre.status_map);

                            reveal(Cache::State::next_by);
                            assert(Cache::State::next_by(cache_pre, cache@, cache_lbl, Cache::Step::access{}));
                            reveal(Cache::State::next);
                        }
                        LoadMapResult::LoadComplete{reads: Ghost(reads)}
                    }
                    FetchErrorCode::CacheFull | FetchErrorCode::NotPresent => {
                        Self::todo_placeholder();
                        unreached()
                    }
                }
            }
        }
    }

    pub fn get_store<'a>(&'a self, key: &Key) -> (out: Option<&'a Value>)
        requires self.wf(),
        ensures
            match out {
                Some(v) => self.store_entries().contains_key(*key) && *v == self.store_entries()[*key],
                None => !self.store_entries().contains_key(*key),
            },
    {
        self.store.get(key)
    }

    pub fn query_value(&self, key: &Key) -> (out: Value)
        requires
            self.wf(),
        ensures
            out == self.kmmap()[*key]->value,
    {
        let got = self.store.get(key);
        let out = match got {
            Some(v) => *v,
            None => Value(0),
        };
        proof {
            match got {
                Some(v) => {
                    assert(self.store_entries().contains_key(*key));
                    assert(*v == self.store_entries()[*key]);
                    assert(self.kmmap()[*key] == Message::Define{value: self.store_entries()[*key]});
                }
                None => {
                    assert(!self.store_entries().contains_key(*key));
                    assert(out == Value(0));
                    assert(self.kmmap()[*key] == Message::empty());
                }
            }
            if !self.store_entries().contains_key(*key) {
                assert(self.kmmap()[*key] == Message::empty());
            }
        }
        out
    }

    pub closed spec fn kmmap(self) -> TotalKMMap {
        view_as_kmmap(self.store)
    }

    pub closed spec fn persistent_store_ptr(self) -> Option<IAddress> {
        self.persistent_store_ptr
    }

    pub closed spec fn persistent_store_ptr_view(self) -> Option<Address> {
        iaddr_view(self.persistent_store_ptr)
    }

    pub proof fn persistent_store_ptr_view_ensures(self)
        ensures
            self.persistent_store_ptr_view() == iaddr_view(self.persistent_store_ptr()),
    {
    }

    pub fn exec_persistent_store_ptr(&self) -> (out: Option<IAddress>)
        ensures out == self.persistent_store_ptr()
    {
        self.persistent_store_ptr
    }

    pub closed spec fn prepared_store_ptr(self) -> Option<IAddress> {
        self.prepared_store_ptr
    }

    pub closed spec fn prepared_store_ptr_view(self) -> Option<Address> {
        iaddr_view(self.prepared_store_ptr)
    }

    pub proof fn prepared_store_ptr_view_ensures(self)
        ensures
            self.prepared_store_ptr_view() == iaddr_view(self.prepared_store_ptr()),
    {
    }

    pub fn exec_prepared_store_ptr(&self) -> (out: Option<IAddress>)
        ensures out == self.prepared_store_ptr()
    {
        self.prepared_store_ptr
    }

    pub closed spec fn prepared_store_lsn(self) -> u64 {
        self.prepared_store_lsn
    }

    pub closed spec fn prepared_store_lsn_nat(self) -> nat {
        self.prepared_store_lsn as nat
    }

    pub fn exec_prepared_store_lsn(&self) -> (out: u64)
        ensures
            out == self.prepared_store_lsn(),
            out as nat == self.prepared_store_lsn_nat(),
    {
        self.prepared_store_lsn
    }

    pub proof fn prepared_store_lsn_nat_ensures(self)
        ensures
            self.prepared_store_lsn_nat() == self.prepared_store_lsn() as nat,
    {
    }

    pub fn set_persistent_store_ptr(&mut self, ptr: Option<IAddress>)
        requires
            old(self).wf(),
            ptr is Some ==> ptr.unwrap().au == old(self).alloc_au(),
            ptr is Some ==> (ptr.unwrap().page as nat) < old(self).next_alloc_page(),
    ensures
        self.wf(),
        self.store_wf(),
        self.persistent_store_ptr() == ptr,
        self.persistent_store_ptr_view() == iaddr_view(ptr),
        self.persistent_store_ptr_matches_alloc_au(),
        self@ == old(self)@,
        self.store_entries() == old(self).store_entries(),
        self.store_lsn() == old(self).store_lsn(),
        self.store_lsn_nat() == old(self).store_lsn_nat(),
        self.alloc_au() == old(self).alloc_au(),
        self.next_alloc_page() == old(self).next_alloc_page(),
    {
        self.persistent_store_ptr = ptr;
        proof {
            if ptr is Some {
                assert(ptr.unwrap().au == old(self).alloc_au());
                assert(self.alloc_au() == old(self).alloc_au());
                assert(ptr.unwrap().au == self.alloc_au());
                assert(ptr.unwrap().au as nat == self.alloc_au() as nat);
            }
        }
    }

    pub fn set_prepared_store(&mut self, ptr: Option<IAddress>, lsn: u64)
        requires
            old(self).wf(),
            old(self).persistent_store_ptr_matches_alloc_au(),
            ptr is Some ==> ptr.unwrap().au == old(self).alloc_au(),
            ptr is Some ==> (ptr.unwrap().page as nat) < old(self).next_alloc_page(),
        ensures
            self.wf(),
            self.store_wf(),
            self.persistent_store_ptr_matches_alloc_au(),
            self.prepared_store_ptr() == ptr,
            self.prepared_store_ptr_view() == iaddr_view(ptr),
            self.prepared_store_lsn() == lsn,
            self.prepared_store_lsn_nat() == lsn as nat,
            self@ == old(self)@,
            self.store_entries() == old(self).store_entries(),
            self.store_lsn() == old(self).store_lsn(),
            self.store_lsn_nat() == old(self).store_lsn_nat(),
            self.persistent_store_ptr() == old(self).persistent_store_ptr(),
            self.persistent_store_ptr_view() == old(self).persistent_store_ptr_view(),
            self.alloc_au() == old(self).alloc_au(),
            self.next_alloc_page() == old(self).next_alloc_page(),
    {
        self.prepared_store_ptr = ptr;
        self.prepared_store_lsn = lsn;
        proof {
            if ptr is Some {
                assert(ptr.unwrap().au == old(self).alloc_au());
                assert(self.alloc_au() == old(self).alloc_au());
                assert(ptr.unwrap().au == self.alloc_au());
                assert(ptr.unwrap().au as nat == self.alloc_au() as nat);
            }
        }
    }

    pub closed spec fn persistent_store_ptr_matches_alloc_au(self) -> bool {
        self.persistent_store_ptr is Some ==> self.persistent_store_ptr.unwrap().au as nat == self.alloc_au() as nat
    }

    pub proof fn persistent_store_ptr_matches_alloc_au_from_ptr(self, ptr: Option<IAddress>)
        requires
            self.wf(),
            self.persistent_store_ptr() == ptr,
            ptr is Some ==> ptr.unwrap().au as nat == self.alloc_au() as nat,
        ensures
            self.persistent_store_ptr_matches_alloc_au(),
    {
        if ptr is Some {
            assert(self.persistent_store_ptr is Some);
            assert(self.persistent_store_ptr.unwrap() == ptr.unwrap());
            assert(ptr.unwrap().au as nat == self.alloc_au() as nat);
        }
    }

    pub proof fn persistent_store_ptr_has_alloc_au(self)
        requires
            self.persistent_store_ptr_matches_alloc_au(),
        ensures
            self.persistent_store_ptr() is Some
                ==> self.persistent_store_ptr().unwrap().au as nat == self.alloc_au() as nat,
    {
    }

    pub proof fn persistent_store_ptr_before_next_alloc(self)
        requires
            self.wf(),
        ensures
            self.persistent_store_ptr() is Some
                ==> (self.persistent_store_ptr().unwrap().page as nat) < self.next_alloc_page(),
    {
    }

    pub proof fn prepared_store_ptr_has_alloc_au(self)
        requires
            self.wf(),
        ensures
            self.prepared_store_ptr() is Some
                ==> self.prepared_store_ptr().unwrap().au as nat == self.alloc_au() as nat,
    {
    }

    pub proof fn prepared_store_ptr_before_next_alloc(self)
        requires
            self.wf(),
        ensures
            self.prepared_store_ptr() is Some
                ==> (self.prepared_store_ptr().unwrap().page as nat) < self.next_alloc_page(),
    {
    }

    pub closed spec fn store_addrs(self, inflight_store_ptr: Option<IAddress>) -> Set<Address>
    {
        let persistent =
            if self.persistent_store_ptr is Some {
                set!{self.persistent_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let prepared =
            if self.prepared_store_ptr is Some {
                set!{self.prepared_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let inflight =
            if inflight_store_ptr is Some {
                set!{inflight_store_ptr.unwrap()@}
            } else {
                set![]
            };
        persistent + prepared + inflight
    }

    pub proof fn store_addrs_are_alloc_au(self, inflight_store_ptr: Option<IAddress>)
        requires
            self.wf(),
            self.persistent_store_ptr_matches_alloc_au(),
            inflight_store_ptr is Some ==> inflight_store_ptr.unwrap().au as nat == self.alloc_au() as nat,
        ensures
            forall |a: Address| #[trigger] self.store_addrs(inflight_store_ptr).contains(a)
                ==> a.au == self.alloc_au() as nat,
    {
        let persistent =
            if self.persistent_store_ptr is Some {
                set!{self.persistent_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let prepared =
            if self.prepared_store_ptr is Some {
                set!{self.prepared_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let inflight =
            if inflight_store_ptr is Some {
                set!{inflight_store_ptr.unwrap()@}
            } else {
                set![]
            };
        assert(self.store_addrs(inflight_store_ptr) == persistent + prepared + inflight);
        assert forall |a: Address| #[trigger] self.store_addrs(inflight_store_ptr).contains(a)
            implies a.au == self.alloc_au() as nat by {
            if self.store_addrs(inflight_store_ptr).contains(a) {
                assert((persistent + prepared + inflight).contains(a));
                if persistent.contains(a) {
                    if self.persistent_store_ptr is Some {
                        assert(a == self.persistent_store_ptr.unwrap()@);
                        assert(self.persistent_store_ptr.unwrap().au as nat == self.alloc_au() as nat);
                        assert(a.au == self.alloc_au() as nat);
                    } else {
                        assert(false);
                    }
                } else if prepared.contains(a) {
                    if self.prepared_store_ptr is Some {
                        assert(a == self.prepared_store_ptr.unwrap()@);
                        assert(self.prepared_store_ptr.unwrap().au as nat == self.alloc_au() as nat);
                        assert(a.au == self.alloc_au() as nat);
                    } else {
                        assert(false);
                    }
                } else {
                    assert(inflight.contains(a));
                    if inflight_store_ptr is Some {
                        assert(a == inflight_store_ptr.unwrap()@);
                        assert(inflight_store_ptr.unwrap().au as nat == self.alloc_au() as nat);
                        assert(a.au == self.alloc_au() as nat);
                    } else {
                        assert(false);
                    }
                }
            }
        };
    }

    pub proof fn store_addrs_none_matches_persistent_view(self)
        ensures
            self.store_addrs(None)
                == (if self.persistent_store_ptr_view() is Some {
                    set!{self.persistent_store_ptr_view().unwrap()}
                } else {
                    set![]
                })
                + (if self.prepared_store_ptr_view() is Some {
                    set!{self.prepared_store_ptr_view().unwrap()}
                } else {
                    set![]
                }),
    {
        let persistent =
            if self.persistent_store_ptr is Some {
                set!{self.persistent_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let prepared =
            if self.prepared_store_ptr is Some {
                set!{self.prepared_store_ptr.unwrap()@}
            } else {
                set![]
            };
        assert(self.persistent_store_ptr_view() == iaddr_view(self.persistent_store_ptr));
        assert(self.prepared_store_ptr_view() == iaddr_view(self.prepared_store_ptr));
        assert(self.store_addrs(None) == persistent + prepared);
        if self.persistent_store_ptr_view() is Some {
            assert(persistent == set!{self.persistent_store_ptr_view().unwrap()});
        } else {
            assert(persistent == Set::<Address>::empty());
        }
        if self.prepared_store_ptr_view() is Some {
            assert(prepared == set!{self.prepared_store_ptr_view().unwrap()});
        } else {
            assert(prepared == Set::<Address>::empty());
        }
    }

    pub proof fn store_addrs_matches_views(self, inflight_store_ptr: Option<IAddress>)
        ensures
            self.store_addrs(inflight_store_ptr)
                == (if self.persistent_store_ptr_view() is Some {
                    set!{self.persistent_store_ptr_view().unwrap()}
                } else {
                    set![]
                })
                + (if self.prepared_store_ptr_view() is Some {
                    set!{self.prepared_store_ptr_view().unwrap()}
                } else {
                    set![]
                })
                + (if inflight_store_ptr is Some {
                    set!{inflight_store_ptr.unwrap()@}
                } else {
                    set![]
                }),
    {
        let persistent =
            if self.persistent_store_ptr is Some {
                set!{self.persistent_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let prepared =
            if self.prepared_store_ptr is Some {
                set!{self.prepared_store_ptr.unwrap()@}
            } else {
                set![]
            };
        let inflight =
            if inflight_store_ptr is Some {
                set!{inflight_store_ptr.unwrap()@}
            } else {
                set![]
            };
        assert(self.persistent_store_ptr_view() == iaddr_view(self.persistent_store_ptr));
        assert(self.store_addrs(inflight_store_ptr) == persistent + prepared + inflight);
        if self.persistent_store_ptr_view() is Some {
            assert(persistent == set!{self.persistent_store_ptr_view().unwrap()});
        } else {
            assert(persistent == Set::<Address>::empty());
        }
    }

    pub closed spec fn is_store_addr(self, inflight_store_ptr: Option<IAddress>, addr: Address) -> bool
    {
        self.store_addrs(inflight_store_ptr).contains(addr)
    }

}

impl View for StoreImpl {
    type V = TotalKMMap;

    open spec fn view(&self) -> Self::V
    {
        self.kmmap()
    }
}

} // verus!
