// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use vstd::prelude::*;

//use vstd::prelude_macros::*;
use verus_state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::{map::*, map_lib::*, seq::*, set::*};

use crate::spec::AsyncDisk_t::{Address, DiskRequest, DiskResponse, RawPage};

verus!{

pub type Slot = usize;

//  Entry is separate from Status because there are some cases
//  where we need to have shared access to the Entry while modifying
//  the Status
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum Status {
    NotFilled,
    Clean,
    Dirty,
    Writeback,
}

pub enum Entry {
    Empty,
    Reserved{addr: Address},
    Loading{addr: Address}, 
    Filled{addr: Address, data: RawPage},
}

impl Entry {
    pub open spec(checked) fn get_addr(self) -> Address 
        recommends !(self is Empty)
    {
        match self {
            Entry::Reserved{addr} => { addr }
            Entry::Loading{addr, ..} => { addr }
            Entry::Filled{addr, ..} => { addr }
            _ => arbitrary()
        }
    }
}

pub open spec fn addr_maps_to_req(requests: Set<DiskRequest>, req: DiskRequest, addr: Address) -> bool
{
    &&& req is ReadReq
    &&& requests.contains(req)
    &&& req->from == addr
}

state_machine!{ Cache {
    fields {
        pub entries: Map<Slot, Entry>,
        pub status_map: Map<Slot, Status>,
        pub lookup_map: Map<Address, Slot>,
    }

    pub enum Label {
        Access{reads: Map<Address, RawPage>, writes: Map<Address, RawPage>},
        EvictableCheck{addrs: Set<Address>},
        DiskOps{requests: Set<DiskRequest>, responses: Map<Address, DiskResponse>},
        Internal,
    }
    
    pub open spec fn empty(slots: nat) -> Self
    {
        Cache::State{
            entries: Map::new(|i: Slot| i < slots , |i| Entry::Empty),
            status_map: Map::new(|i: Slot| i < slots , |i| Status::NotFilled),
            lookup_map: Map::empty(),
        }
    }

    pub open spec fn valid_read(self, addr: Address, data: RawPage) -> bool 
    {
        &&& self.lookup_map.contains_key(addr)
        &&& self.entries[self.lookup_map[addr]] is Filled
        &&& data == self.entries[self.lookup_map[addr]]->data
    }

    pub open spec fn valid_write(self, addr: Address) -> bool 
    {
        &&& self.lookup_map.contains_key(addr) 
        &&& match self.entries[self.lookup_map[addr]] {
            Entry::Reserved{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && !(self.status_map[self.lookup_map[addr]] is Writeback),
            _ => false,
        }
    }

    pub open spec(checked) fn valid_new_slots_mapping(self, mapping: Map<Slot, Address>) -> bool 
    {
        // 1 address can't be mapped to 2 slots
        &&& mapping.is_injective()
        // ensures that new slots are within the valid range
        &&& mapping.dom() <= self.entries.dom()
        // new slots cannot overlap with existing look up entries
        &&& mapping.values().disjoint(self.lookup_map.dom())
        // new slots must be empty
        &&& forall |slot| #[trigger] mapping.contains_key(slot) ==> self.entries[slot] is Empty
    }

    // reserve is only used for bypass writes
    // NOTE: how do we imagine reserve to work
    // bypass writes just reserve spots first, they are reserved for these addresses
    // this brings the lookup map up to date so we can retrieve those pages safely
    // with promises that those pages are present in the look up map
    // inv => tracks that physical state matches with model status

    transition!{ reserve(lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        require lbl is Internal;
        require pre.valid_new_slots_mapping(new_slots_mapping);

        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Reserved{addr: new_slots_mapping[slot]}
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

    pub open spec fn valid_load_requests(requests: Set<DiskRequest>, new_slots_mapping: Map<Slot, Address>) -> bool 
    {
        &&& forall |req| #[trigger] requests.contains(req) ==> req is ReadReq
        &&& forall |addr| new_slots_mapping.contains_value(addr) <==> exists |req| #[trigger] addr_maps_to_req(requests, req, addr)
    }

    transition!{ load_initiate(lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        require let Label::DiskOps{requests, responses} = lbl;
        require !requests.is_empty();
        require responses.is_empty();

        require pre.valid_new_slots_mapping(new_slots_mapping);
        require Self::valid_load_requests(requests, new_slots_mapping);

        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Loading{addr: new_slots_mapping[slot]}
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

    pub open spec fn valid_load_responses(self, responses: Map<Address, DiskResponse>) -> bool
    {
        forall |addr| #[trigger] responses.contains_key(addr) ==> {
            &&& responses[addr] is ReadResp
            &&& self.lookup_map.contains_key(addr)
            &&& self.entries[self.lookup_map[addr]] is Loading
        }
    }

    // receive read responses from disk
    transition!{ load_complete(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();
        require pre.valid_load_responses(responses);

        let slot_addr_map = pre.lookup_map.restrict(responses.dom()).invert();
        let updated_entries = Map::new(
            |slot| slot_addr_map.contains_key(slot),
            |slot| Entry::Filled{
                addr: slot_addr_map[slot],
                data: responses[slot_addr_map[slot]]->data
            }
        );

        let updated_status_map = Map::new(
            |slot| slot_addr_map.contains_key(slot),
            |slot| Status::Clean
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    pub open spec fn write_updated_entries(self, writes: Map<Address, RawPage>) -> Map<Slot, Entry>
    {
        let write_slots = self.lookup_map.restrict(writes.dom()).values();
        Map::new(
            |slot| write_slots.contains(slot),
            |slot| Entry::Filled{
                addr: self.entries[slot].get_addr(), 
                data: writes[self.entries[slot].get_addr()]
            })
    }

    pub open spec fn write_updated_status(self, writes: Map<Address, RawPage>) -> Map<Slot, Status>
    {
        let write_slots = self.lookup_map.restrict(writes.dom()).values();
        Map::new(
            |slot| write_slots.contains(slot),
            |slot| Status::Dirty
        )
    }

    // NOTE: access must enable batched accesses because program
    // model needs to make batch updates as an atomic transition
    transition!{ access(lbl: Label) {
        require lbl is Access;
        require forall |addr| #[trigger] lbl->reads.contains_key(addr) 
            ==> pre.valid_read(addr, lbl->reads[addr]);
        require forall |addr| #[trigger] lbl->writes.contains_key(addr) 
            ==> pre.valid_write(addr);

        let updated_entries = pre.write_updated_entries(lbl->writes);
        let updated_status_map = pre.write_updated_status(lbl->writes);

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    pub open spec fn valid_writeback_requests(self, requests: Set<DiskRequest>) -> bool 
    {
        forall |req| #[trigger] requests.contains(req) ==> {
            &&& req is WriteReq
            &&& self.lookup_map.contains_key(req->to)
            &&& self.entries[self.lookup_map[req->to]] == Entry::Filled{addr: req->to, data: req->data}
            &&& self.status_map[self.lookup_map[req->to]] is Dirty
        }
    }

    transition!{ writeback_initiate(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require !requests.is_empty();
        require responses.is_empty();
        require pre.valid_writeback_requests(requests);

        let writeback_slots = Map::new(|req: DiskRequest| requests.contains(req), |req: DiskRequest| pre.lookup_map[req->to]).values();
        let updated_status_map = Map::new(|slot| writeback_slots.contains(slot), |slot| Status::Writeback{});

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    pub open spec fn valid_writeback_responses(self, responses: Map<Address, DiskResponse>) -> bool
    {
        forall |addr| #[trigger] responses.contains_key(addr) ==> {
            &&& responses[addr] is WriteResp
            &&& self.lookup_map.contains_key(addr)
            &&& self.entries[self.lookup_map[addr]] is Filled
            &&& self.status_map[self.lookup_map[addr]] is Writeback
        }
    }

    // receive write responses from disk
    transition!{ writeback_complete(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();
        require pre.valid_writeback_responses(responses);

        let resps_slots = pre.lookup_map.restrict(responses.dom()).values();
        let updated_status_map = Map::new(
            |slot| resps_slots.contains(slot),
            |slot| Status::Clean
        );

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    transition!{ evict(lbl: Label, evicted_slots: Set<Slot>) {
        // eviction of pages should be seen as internal or not
        // I guess this is an invalidate page access, we can imagine 
        // the difference is when the cache is required to enforce it, 
        // if it's not enforced right away then. the question is is it ever possible
        // for us to discard journal pages that have never been marshalled and 

        require lbl is Internal;
        require evicted_slots <= pre.entries.dom();
        require forall |slot| #[trigger] evicted_slots.contains(slot) ==> {        
            &&& pre.entries[slot] is Filled
            &&& pre.status_map[slot] is Clean
        };

        let evicted_addrs = Map::new(|slot| evicted_slots.contains(slot), |slot| pre.entries[slot].get_addr()).values();
        let updated_entries = Map::new(|slot| evicted_slots.contains(slot), |slot| Entry::Empty);
        let updated_status_map = Map::new(|slot| evicted_slots.contains(slot), |slot| Status::NotFilled);

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
        update lookup_map = pre.lookup_map.remove_keys(evicted_addrs);
    }}

    transition!{ evictable(lbl: Label) {
        require lbl is EvictableCheck;
        require forall |addr| lbl->addrs.contains(addr) 
            &&  #[trigger] pre.lookup_map.contains_key(addr)
            ==> {
                &&& pre.entries[pre.lookup_map[addr]] is Filled
                &&& pre.status_map[pre.lookup_map[addr]] is Clean
            };
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Internal;
    }}

    init!{ initialize(slots: nat) {
        init entries = Map::new(|i: Slot| i < slots , |i| Entry::Empty);
        init status_map = Map::new(|i: Slot| i < slots , |i| Status::NotFilled);
        init lookup_map = Map::empty();
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        // slots hold unique addres
        &&& self.slots_hold_unique_addr()
        &&& self.status_map.dom() =~= self.entries.dom()
        &&& self.lookup_map == self.build_lookup_map()
        &&& forall |slot| #[trigger] self.status_map.contains_key(slot)
            ==> ( (self.status_map[slot] is NotFilled) <==> !(self.entries[slot] is Filled) )
    }

    pub open spec fn build_lookup_map(self) -> Map<Address, Slot>
    {
        let slot_addr_map = Map::new(
            |slot| self.non_empty_slot(slot),
            |slot| self.entries[slot].get_addr()
        );
        slot_addr_map.invert()
    }

    pub open spec fn non_empty_slot(self, slot: Slot) -> bool
    {
        &&& self.entries.contains_key(slot) 
        &&& !(self.entries[slot] is Empty)
    }

    pub open spec fn slots_hold_unique_addr(self) -> bool
    {
        forall |s1, s2| #[trigger] self.non_empty_slot(s1)
            && #[trigger] self.non_empty_slot(s2) && s1 != s2 
        ==> self.entries[s1].get_addr() != self.entries[s2].get_addr()
    }

    pub proof fn build_lookup_map_ensures(self)
    requires self.slots_hold_unique_addr()
    ensures ({
        let lookup_map = self.build_lookup_map();
        self.build_lookup_map_props(lookup_map)
    }) {
        let lookup_map = self.build_lookup_map();
        reveal(Cache::State::build_lookup_map);

        let slot_addr_map = Map::new(
            |slot| self.non_empty_slot(slot),
            |slot| self.entries[slot].get_addr()
        );

        assert(lookup_map == slot_addr_map.invert());

        // Prove the non-empty-slot map is injective using unique addresses.
        assert(slot_addr_map.is_injective()) by {
            assert forall |s1: Slot, s2: Slot|
                s1 != s2
                && slot_addr_map.contains_key(s1)
                && slot_addr_map.contains_key(s2)
                implies #[trigger] slot_addr_map[s1] != #[trigger] slot_addr_map[s2]
            by {
                assert(self.entries.contains_key(s1));
                assert(self.entries.contains_key(s2));
                assert(self.non_empty_slot(s1));
                assert(self.non_empty_slot(s2));
                assert(self.entries[s1].get_addr() != self.entries[s2].get_addr());
                assert(slot_addr_map[s1] == self.entries[s1].get_addr());
                assert(slot_addr_map[s2] == self.entries[s2].get_addr());
            }
        }

        // Invert of any map is injective; plus the inverse agrees on original keys.
        slot_addr_map.lemma_invert_is_injective();

        assert(self.build_lookup_map_props(lookup_map)) by {
            assert(lookup_map.is_injective()) by {
                assert(lookup_map == slot_addr_map.invert());
                assert(slot_addr_map.invert().is_injective());
            }

            assert forall |addr| #[trigger] lookup_map.contains_key(addr) implies {
                let slot = lookup_map[addr];
                &&& self.entries.contains_key(slot)
                &&& !(self.entries[slot] is Empty)
                &&& self.entries[slot].get_addr() == addr
            } by {
                // Unfold invert to relate lookup_map to the non-empty-slot map.
                reveal(Map::invert);
                assert(lookup_map == slot_addr_map.invert());
                assert(slot_addr_map.contains_value(addr)) by {
                    assert(lookup_map.contains_key(addr));
                }
                let s = choose |s: Slot| #[trigger] slot_addr_map.contains_key(s)
                    && slot_addr_map[s] == addr;
                assert(slot_addr_map.contains_pair(s, addr));
                assert(lookup_map[addr] == s);
                assert(slot_addr_map.contains_pair(lookup_map[addr], addr));
                assert(self.entries.contains_key(lookup_map[addr]));
                assert(!(self.entries[lookup_map[addr]] is Empty));
                assert(slot_addr_map[lookup_map[addr]] == self.entries[lookup_map[addr]].get_addr());
                assert(slot_addr_map[lookup_map[addr]] == addr);
            }

            assert forall |slot| #[trigger] self.entries.contains_key(slot) && !(self.entries[slot] is Empty)
            implies {
                let addr = self.entries[slot].get_addr();
                lookup_map.contains_key(addr) && lookup_map[addr] == slot
            } by {
                let addr = self.entries[slot].get_addr();
                assert(slot_addr_map.contains_pair(slot, addr));
                assert(slot_addr_map.contains_value(addr));
                reveal(Map::invert);
                assert(lookup_map == slot_addr_map.invert());
                assert(lookup_map.contains_key(addr)) by {
                    assert(slot_addr_map.contains_value(addr));
                }
                assert(slot_addr_map[slot] == addr);
                assert(slot_addr_map.contains_pair(lookup_map[addr], addr)) by {
                    assert(lookup_map.contains_key(addr));
                    assert(slot_addr_map.contains_value(addr));
                    let s = choose |s: Slot| slot_addr_map.contains_pair(s, addr);
                    assert(slot_addr_map.contains_pair(s, addr));
                    assert(lookup_map[addr] == s);
                }
                assert(slot_addr_map.contains_key(slot));
                assert(slot_addr_map.contains_key(lookup_map[addr]));
                if lookup_map[addr] != slot {
                    assert(slot_addr_map[lookup_map[addr]] != slot_addr_map[slot]) by {
                        assert(slot_addr_map.is_injective());
                    }
                    assert(slot_addr_map[lookup_map[addr]] == addr);
                    assert(false);
                }
            }
        }
    }

    pub open spec fn build_lookup_map_props(self, lookup_map: Map<Address, Slot>) -> bool
    {
        &&& lookup_map.is_injective()
        &&& forall |addr| #[trigger] lookup_map.contains_key(addr) ==> {
            let slot = lookup_map[addr];
            &&& self.entries.contains_key(slot)
            &&& !(self.entries[slot] is Empty)
            &&& self.entries[slot].get_addr() == addr
        }
        &&& forall |slot| #[trigger] self.entries.contains_key(slot) && !(self.entries[slot] is Empty) ==> {
                let addr = self.entries[slot].get_addr();
                lookup_map.contains_key(addr) && lookup_map[addr] == slot
        }
    }

    pub proof fn build_lookup_map_is_unique(self, candidate: Map<Address, Slot>)
        requires
            self.slots_hold_unique_addr(),
            self.build_lookup_map_props(candidate),
        ensures
            candidate =~= self.build_lookup_map(),
    {
        self.build_lookup_map_ensures();
        let canonical = self.build_lookup_map();
        assert(self.build_lookup_map_props(canonical));

        assert forall |addr| #[trigger] candidate.contains_key(addr) implies {
            canonical.contains_key(addr) && candidate[addr] == canonical[addr]
        } by {
            let slot = candidate[addr];
            assert(self.entries.contains_key(slot));
            assert(!(self.entries[slot] is Empty));
            assert(self.entries[slot].get_addr() == addr);
            assert(canonical.contains_key(addr));
            assert(canonical[addr] == slot);
        }

        assert forall |addr| #[trigger] canonical.contains_key(addr) implies {
            candidate.contains_key(addr) && canonical[addr] == candidate[addr]
        } by {
            let slot = canonical[addr];
            assert(self.entries.contains_key(slot));
            assert(!(self.entries[slot] is Empty));
            assert(self.entries[slot].get_addr() == addr);
            assert(candidate.contains_key(addr));
            assert(candidate[addr] == slot);
        }

        assert(candidate =~= canonical);
    }

    pub proof fn union_prefer_right_preserves_dom_entry(base: Map<Slot, Entry>, updates: Map<Slot, Entry>)
        requires updates.dom() <= base.dom()
        ensures base.union_prefer_right(updates).dom() =~= base.dom()
    {
        let merged = base.union_prefer_right(updates);
        assert forall |slot| #[trigger] merged.contains_key(slot) <==> base.contains_key(slot) by {
            if merged.contains_key(slot) {
                if updates.contains_key(slot) {
                    assert(base.contains_key(slot));
                } else {
                    assert(base.contains_key(slot));
                }
            }
            if base.contains_key(slot) {
                assert(merged.contains_key(slot));
            }
        }
    }

    pub proof fn union_prefer_right_preserves_dom_status(base: Map<Slot, Status>, updates: Map<Slot, Status>)
        requires updates.dom() <= base.dom()
        ensures base.union_prefer_right(updates).dom() =~= base.dom()
    {
        let merged = base.union_prefer_right(updates);
        assert forall |slot| #[trigger] merged.contains_key(slot) <==> base.contains_key(slot) by {
            if merged.contains_key(slot) {
                if updates.contains_key(slot) {
                    assert(base.contains_key(slot));
                } else {
                    assert(base.contains_key(slot));
                }
            }
            if base.contains_key(slot) {
                assert(merged.contains_key(slot));
            }
        }
    }

    pub proof fn remove_keys_dom(base: Map<Address, Slot>, keys: Set<Address>)
        ensures
            base.remove_keys(keys).dom() =~= base.dom().difference(keys)
    {
        let reduced = base.remove_keys(keys);
        assert forall |addr| #[trigger] reduced.contains_key(addr) <==> base.dom().difference(keys).contains(addr) by {
            if reduced.contains_key(addr) {
                assert(base.contains_key(addr));
                assert(!keys.contains(addr));
            }
            if base.dom().difference(keys).contains(addr) {
                assert(base.contains_key(addr));
                assert(!keys.contains(addr));
                assert(reduced.contains_key(addr));
            }
        }
    }

    pub proof fn invert_contains_pair<K, V>(map: Map<K, V>, value: V)
        requires
            map.contains_value(value),
        ensures
            map.contains_pair(map.invert()[value], value),
    {
        assert(exists |key: K| map.contains_pair(key, value)) by {
            let key = choose |key: K| map.contains_key(key) && map[key] == value;
            assert(map.contains_pair(key, value));
        }
        let key = choose |key: K| map.contains_pair(key, value);
        assert(map.contains_pair(key, value));
        reveal(Map::invert);
        assert(map.invert()[value] == key);
        assert(map.contains_pair(map.invert()[value], value));
    }


    #[inductive(reserve)]
    fn reserve_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) { 
        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Reserved{addr: new_slots_mapping[slot]}
        );

        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();

        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                let a1 = post.entries[s1].get_addr();
                let a2 = post.entries[s2].get_addr();
                if new_slots_mapping.contains_key(s1) {
                    if new_slots_mapping.contains_key(s2) {
                        assert(a1 == new_slots_mapping[s1]);
                        assert(a2 == new_slots_mapping[s2]);
                        assert(a1 != a2) by {
                            assert(new_slots_mapping.is_injective());
                        }
                    } else {
                        assert(pre.entries[s2] == post.entries[s2]);
                        assert(pre.non_empty_slot(s2));
                        assert(pre.lookup_map.contains_key(a2));
                        assert(!new_slots_mapping.values().contains(a2));
                        assert(a1 == new_slots_mapping[s1]);
                    }
                } else {
                    if new_slots_mapping.contains_key(s2) {
                        assert(pre.entries[s1] == post.entries[s1]);
                        assert(pre.non_empty_slot(s1));
                        assert(pre.lookup_map.contains_key(a1));
                        assert(!new_slots_mapping.values().contains(a1));
                        assert(a2 == new_slots_mapping[s2]);
                    } else {
                        assert(pre.entries[s1] == post.entries[s1]);
                        assert(pre.entries[s2] == post.entries[s2]);
                        assert(pre.non_empty_slot(s1));
                        assert(pre.non_empty_slot(s2));
                        assert(a1 != a2);
                    }
                }
            }
        }

        Self::union_prefer_right_preserves_dom_entry(pre.entries, updated_entries);
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.status_map.dom() =~= post.entries.dom());

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if new_slots_mapping.contains_key(slot) {
                assert(post.status_map[slot] is NotFilled);
                assert(!(post.entries[slot] is Filled));
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }

        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) implies {
                let slot = post.lookup_map[addr];
                &&& post.entries.contains_key(slot)
                &&& !(post.entries[slot] is Empty)
                &&& post.entries[slot].get_addr() == addr
            } by {
                if new_slots_mapping.invert().contains_key(addr) {
                    let slot = new_slots_mapping.invert()[addr];
                    Self::invert_contains_pair(new_slots_mapping, addr);
                    assert(post.lookup_map[addr] == slot);
                    assert(post.entries[slot] == Entry::Reserved{addr});
                } else {
                    assert(pre.lookup_map.contains_key(addr));
                    let slot = pre.lookup_map[addr];
                    assert(post.lookup_map[addr] == slot);
                    assert(pre.entries.contains_key(slot));
                    assert(!(pre.entries[slot] is Empty));
                    assert(post.entries[slot] == pre.entries[slot]);
                }
            }

            assert forall |slot| #[trigger] post.entries.contains_key(slot) && !(post.entries[slot] is Empty) implies {
                let addr = post.entries[slot].get_addr();
                post.lookup_map.contains_key(addr) && post.lookup_map[addr] == slot
            } by {
                let addr = post.entries[slot].get_addr();
                if new_slots_mapping.contains_key(slot) {
                    assert(addr == new_slots_mapping[slot]);
                    assert(new_slots_mapping.invert().contains_key(addr));
                    Self::invert_contains_pair(new_slots_mapping, addr);
                    assert(post.lookup_map.contains_key(addr));
                    assert(post.lookup_map[addr] == slot);
                } else {
                    assert(post.entries[slot] == pre.entries[slot]);
                    assert(pre.entries.contains_key(slot));
                    assert(!(pre.entries[slot] is Empty));
                    assert(pre.lookup_map.contains_key(addr));
                    assert(pre.lookup_map[addr] == slot);
                    assert(!new_slots_mapping.values().contains(addr));
                    assert(post.lookup_map.contains_key(addr));
                    assert(post.lookup_map[addr] == slot);
                }
            }

            assert(post.lookup_map.is_injective()) by {
                assert forall |a1: Address, a2: Address|
                    post.lookup_map.contains_key(a1)
                    && post.lookup_map.contains_key(a2)
                    && a1 != a2
                    implies #[trigger] post.lookup_map[a1] != #[trigger] post.lookup_map[a2]
                by {
                    let s1 = post.lookup_map[a1];
                    let s2 = post.lookup_map[a2];
                    if s1 == s2 {
                        assert(post.entries[s1].get_addr() == a1);
                        assert(post.entries[s2].get_addr() == a2);
                        assert(a1 == a2);
                        assert(false);
                    }
                }
            }
        }
        post.build_lookup_map_is_unique(post.lookup_map);
    }
    
    #[inductive(load_initiate)]
    fn load_initiate_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Loading{addr: new_slots_mapping[slot]}
        );

        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();

        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                let a1 = post.entries[s1].get_addr();
                let a2 = post.entries[s2].get_addr();
                if new_slots_mapping.contains_key(s1) {
                    if new_slots_mapping.contains_key(s2) {
                        assert(a1 == new_slots_mapping[s1]);
                        assert(a2 == new_slots_mapping[s2]);
                        assert(a1 != a2) by {
                            assert(new_slots_mapping.is_injective());
                        }
                    } else {
                        assert(pre.entries[s2] == post.entries[s2]);
                        assert(pre.non_empty_slot(s2));
                        assert(pre.lookup_map.contains_key(a2));
                        assert(!new_slots_mapping.values().contains(a2));
                        assert(a1 == new_slots_mapping[s1]);
                    }
                } else {
                    if new_slots_mapping.contains_key(s2) {
                        assert(pre.entries[s1] == post.entries[s1]);
                        assert(pre.non_empty_slot(s1));
                        assert(pre.lookup_map.contains_key(a1));
                        assert(!new_slots_mapping.values().contains(a1));
                        assert(a2 == new_slots_mapping[s2]);
                    } else {
                        assert(pre.entries[s1] == post.entries[s1]);
                        assert(pre.entries[s2] == post.entries[s2]);
                        assert(pre.non_empty_slot(s1));
                        assert(pre.non_empty_slot(s2));
                        assert(a1 != a2);
                    }
                }
            }
        }

        Self::union_prefer_right_preserves_dom_entry(pre.entries, updated_entries);
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.status_map.dom() =~= post.entries.dom());

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if new_slots_mapping.contains_key(slot) {
                assert(post.status_map[slot] is NotFilled);
                assert(!(post.entries[slot] is Filled));
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }

        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) implies {
                let slot = post.lookup_map[addr];
                &&& post.entries.contains_key(slot)
                &&& !(post.entries[slot] is Empty)
                &&& post.entries[slot].get_addr() == addr
            } by {
                if new_slots_mapping.invert().contains_key(addr) {
                    let slot = new_slots_mapping.invert()[addr];
                    Self::invert_contains_pair(new_slots_mapping, addr);
                    assert(post.lookup_map[addr] == slot);
                    assert(post.entries[slot] == Entry::Loading{addr});
                } else {
                    assert(pre.lookup_map.contains_key(addr));
                    let slot = pre.lookup_map[addr];
                    assert(post.lookup_map[addr] == slot);
                    assert(pre.entries.contains_key(slot));
                    assert(!(pre.entries[slot] is Empty));
                    assert(post.entries[slot] == pre.entries[slot]);
                }
            }

            assert forall |slot| #[trigger] post.entries.contains_key(slot) && !(post.entries[slot] is Empty) implies {
                let addr = post.entries[slot].get_addr();
                post.lookup_map.contains_key(addr) && post.lookup_map[addr] == slot
            } by {
                let addr = post.entries[slot].get_addr();
                if new_slots_mapping.contains_key(slot) {
                    assert(addr == new_slots_mapping[slot]);
                    assert(new_slots_mapping.invert().contains_key(addr));
                    Self::invert_contains_pair(new_slots_mapping, addr);
                    assert(post.lookup_map.contains_key(addr));
                    assert(post.lookup_map[addr] == slot);
                } else {
                    assert(post.entries[slot] == pre.entries[slot]);
                    assert(pre.entries.contains_key(slot));
                    assert(!(pre.entries[slot] is Empty));
                    assert(pre.lookup_map.contains_key(addr));
                    assert(pre.lookup_map[addr] == slot);
                    assert(!new_slots_mapping.values().contains(addr));
                    assert(post.lookup_map.contains_key(addr));
                    assert(post.lookup_map[addr] == slot);
                }
            }

            assert(post.lookup_map.is_injective()) by {
                assert forall |a1: Address, a2: Address|
                    post.lookup_map.contains_key(a1)
                    && post.lookup_map.contains_key(a2)
                    && a1 != a2
                    implies #[trigger] post.lookup_map[a1] != #[trigger] post.lookup_map[a2]
                by {
                    let s1 = post.lookup_map[a1];
                    let s2 = post.lookup_map[a2];
                    if s1 == s2 {
                        assert(post.entries[s1].get_addr() == a1);
                        assert(post.entries[s2].get_addr() == a2);
                        assert(a1 == a2);
                        assert(false);
                    }
                }
            }
        }
        post.build_lookup_map_is_unique(post.lookup_map);
    }
    
    #[inductive(load_complete)]
    fn load_complete_inductive(pre: Self, post: Self, lbl: Label) { 
        let slot_addr_map = pre.lookup_map.restrict(lbl->responses.dom()).invert();
        let updated_entries = Map::new(
            |slot| slot_addr_map.contains_key(slot),
            |slot| Entry::Filled{
                addr: slot_addr_map[slot],
                data: lbl->responses[slot_addr_map[slot]]->data
            }
        );
        let updated_status_map = Map::new(
            |slot| slot_addr_map.contains_key(slot),
            |slot| Status::Clean
        );

        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();

        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                if slot_addr_map.contains_key(s1) {
                    assert(post.entries[s1].get_addr() == slot_addr_map[s1]);
                    Self::invert_contains_pair(pre.lookup_map.restrict(lbl->responses.dom()), s1);
                    assert(pre.lookup_map[slot_addr_map[s1]] == s1);
                } else {
                    assert(post.entries[s1] == pre.entries[s1]);
                }
                if slot_addr_map.contains_key(s2) {
                    assert(post.entries[s2].get_addr() == slot_addr_map[s2]);
                    Self::invert_contains_pair(pre.lookup_map.restrict(lbl->responses.dom()), s2);
                    assert(pre.lookup_map[slot_addr_map[s2]] == s2);
                } else {
                    assert(post.entries[s2] == pre.entries[s2]);
                }
                assert(pre.entries[s1].get_addr() == post.entries[s1].get_addr());
                assert(pre.entries[s2].get_addr() == post.entries[s2].get_addr());
                assert(pre.non_empty_slot(s1));
                assert(pre.non_empty_slot(s2));
                assert(pre.entries[s1].get_addr() != pre.entries[s2].get_addr());
            }
        }

        Self::union_prefer_right_preserves_dom_entry(pre.entries, updated_entries);
        Self::union_prefer_right_preserves_dom_status(pre.status_map, updated_status_map);
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.status_map.dom() =~= post.entries.dom());

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if slot_addr_map.contains_key(slot) {
                assert(post.status_map[slot] is Clean);
                assert(post.entries[slot] is Filled);
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }

        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert(post.lookup_map == pre.lookup_map);
            assert(post.lookup_map.is_injective());

            assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) implies {
                let slot = post.lookup_map[addr];
                &&& post.entries.contains_key(slot)
                &&& !(post.entries[slot] is Empty)
                &&& post.entries[slot].get_addr() == addr
            } by {
                let slot = post.lookup_map[addr];
                assert(pre.lookup_map.contains_key(addr));
                assert(pre.lookup_map[addr] == slot);
                if slot_addr_map.contains_key(slot) {
                    Self::invert_contains_pair(pre.lookup_map.restrict(lbl->responses.dom()), slot);
                    assert(slot_addr_map[slot] == addr);
                    assert(post.entries[slot] is Filled);
                    assert(post.entries[slot].get_addr() == addr);
                } else {
                    assert(post.entries[slot] == pre.entries[slot]);
                    assert(!(post.entries[slot] is Empty));
                    assert(post.entries[slot].get_addr() == addr);
                }
            }

            assert forall |slot| #[trigger] post.entries.contains_key(slot) && !(post.entries[slot] is Empty) implies {
                let addr = post.entries[slot].get_addr();
                post.lookup_map.contains_key(addr) && post.lookup_map[addr] == slot
            } by {
                let addr = post.entries[slot].get_addr();
                assert(pre.entries.contains_key(slot));
                if slot_addr_map.contains_key(slot) {
                    assert(slot_addr_map[slot] == addr);
                    assert(pre.lookup_map.contains_key(addr));
                    assert(pre.lookup_map[addr] == slot);
                } else {
                    assert(post.entries[slot] == pre.entries[slot]);
                    assert(!(pre.entries[slot] is Empty));
                    assert(pre.lookup_map.contains_key(addr));
                    assert(pre.lookup_map[addr] == slot);
                }
                assert(post.lookup_map.contains_key(addr));
                assert(post.lookup_map[addr] == slot);
            }
        }
        post.build_lookup_map_is_unique(post.lookup_map);
    }

    #[inductive(access)]
    fn access_inductive(pre: Self, post: Self, lbl: Label) { 
        let updated_entries = pre.write_updated_entries(lbl->writes);
        let updated_status_map = pre.write_updated_status(lbl->writes);

        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();

        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                if updated_entries.contains_key(s1) {
                    assert(post.entries[s1].get_addr() == pre.entries[s1].get_addr());
                } else {
                    assert(post.entries[s1] == pre.entries[s1]);
                }
                if updated_entries.contains_key(s2) {
                    assert(post.entries[s2].get_addr() == pre.entries[s2].get_addr());
                } else {
                    assert(post.entries[s2] == pre.entries[s2]);
                }
                assert(pre.non_empty_slot(s1));
                assert(pre.non_empty_slot(s2));
                assert(pre.entries[s1].get_addr() != pre.entries[s2].get_addr());
            }
        }

        Self::union_prefer_right_preserves_dom_entry(pre.entries, updated_entries);
        Self::union_prefer_right_preserves_dom_status(pre.status_map, updated_status_map);
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.status_map.dom() =~= post.entries.dom());

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if updated_entries.contains_key(slot) {
                assert(post.entries[slot] is Filled);
                assert(post.status_map[slot] is Dirty);
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }

        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert(post.lookup_map == pre.lookup_map);
            assert(post.lookup_map.is_injective());

            assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) implies {
                let slot = post.lookup_map[addr];
                &&& post.entries.contains_key(slot)
                &&& !(post.entries[slot] is Empty)
                &&& post.entries[slot].get_addr() == addr
            } by {
                let slot = post.lookup_map[addr];
                assert(pre.lookup_map.contains_key(addr));
                assert(pre.lookup_map[addr] == slot);
                if updated_entries.contains_key(slot) {
                    assert(post.entries[slot].get_addr() == pre.entries[slot].get_addr());
                } else {
                    assert(post.entries[slot] == pre.entries[slot]);
                }
                assert(post.entries[slot].get_addr() == addr);
            }

            assert forall |slot| #[trigger] post.entries.contains_key(slot) && !(post.entries[slot] is Empty) implies {
                let addr = post.entries[slot].get_addr();
                post.lookup_map.contains_key(addr) && post.lookup_map[addr] == slot
            } by {
                let addr = post.entries[slot].get_addr();
                assert(pre.entries.contains_key(slot));
                if updated_entries.contains_key(slot) {
                    assert(pre.lookup_map.contains_key(addr));
                    assert(pre.lookup_map[addr] == slot);
                } else {
                    assert(post.entries[slot] == pre.entries[slot]);
                    assert(!(pre.entries[slot] is Empty));
                    assert(pre.lookup_map.contains_key(addr));
                    assert(pre.lookup_map[addr] == slot);
                }
                assert(post.lookup_map.contains_key(addr));
                assert(post.lookup_map[addr] == slot);
            }
        }
        post.build_lookup_map_is_unique(post.lookup_map);
    }
    
    #[inductive(writeback_initiate)]
    fn writeback_initiate_inductive(pre: Self, post: Self, lbl: Label) { 
        let writeback_slots = Map::new(|req: DiskRequest| lbl->requests.contains(req), |req: DiskRequest| pre.lookup_map[req->to]).values();
        let updated_status_map = Map::new(|slot| writeback_slots.contains(slot), |slot| Status::Writeback{});

        assert(post.entries == pre.entries);
        assert(post.lookup_map == pre.lookup_map);
        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();
        assert(pre.build_lookup_map_props(pre.lookup_map));
        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                assert(post.entries[s1] == pre.entries[s1]);
                assert(post.entries[s2] == pre.entries[s2]);
                assert(pre.non_empty_slot(s1));
                assert(pre.non_empty_slot(s2));
                assert(pre.entries[s1].get_addr() != pre.entries[s2].get_addr());
            }
        }
        assert(updated_status_map.dom() <= pre.status_map.dom()) by {
            assert forall |slot| #[trigger] updated_status_map.contains_key(slot) implies pre.status_map.contains_key(slot) by {
                let req = choose |req: DiskRequest| lbl->requests.contains(req) && pre.lookup_map[req->to] == slot;
                assert(pre.valid_writeback_requests(lbl->requests));
                assert(pre.lookup_map.contains_key(req->to));
                assert(pre.lookup_map[req->to] == slot);
                assert(pre.entries.contains_key(slot));
                assert(pre.status_map.contains_key(slot));
            }
        }
        Self::union_prefer_right_preserves_dom_status(pre.status_map, updated_status_map);
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= post.entries.dom());
        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert(post.lookup_map == pre.lookup_map);
            assert(post.entries == pre.entries);
            assert(pre.build_lookup_map_props(pre.lookup_map));
        }
        post.build_lookup_map_is_unique(post.lookup_map);

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if updated_status_map.contains_key(slot) {
                assert(post.status_map[slot] is Writeback);
                assert(post.entries[slot] is Filled);
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }
    }
    
    #[inductive(writeback_complete)]
    fn writeback_complete_inductive(pre: Self, post: Self, lbl: Label) { 
        let resp_slots = pre.lookup_map.restrict(lbl->responses.dom()).values();
        let updated_status_map = Map::new(
            |slot| resp_slots.contains(slot),
            |slot| Status::Clean
        );

        assert(post.entries == pre.entries);
        assert(post.lookup_map == pre.lookup_map);
        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();
        assert(pre.build_lookup_map_props(pre.lookup_map));
        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                assert(post.entries[s1] == pre.entries[s1]);
                assert(post.entries[s2] == pre.entries[s2]);
                assert(pre.non_empty_slot(s1));
                assert(pre.non_empty_slot(s2));
                assert(pre.entries[s1].get_addr() != pre.entries[s2].get_addr());
            }
        }
        assert(updated_status_map.dom() <= pre.status_map.dom()) by {
            assert forall |slot| #[trigger] updated_status_map.contains_key(slot) implies pre.status_map.contains_key(slot) by {
                let addr = choose |addr: Address| lbl->responses.contains_key(addr) && pre.lookup_map[addr] == slot;
                assert(pre.valid_writeback_responses(lbl->responses));
                assert(pre.lookup_map.contains_key(addr));
                assert(pre.lookup_map[addr] == slot);
                assert(pre.entries.contains_key(slot));
                assert(pre.status_map.contains_key(slot));
            }
        }
        Self::union_prefer_right_preserves_dom_status(pre.status_map, updated_status_map);
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= post.entries.dom());
        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert(post.lookup_map == pre.lookup_map);
            assert(post.entries == pre.entries);
            assert(pre.build_lookup_map_props(pre.lookup_map));
        }
        post.build_lookup_map_is_unique(post.lookup_map);

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if updated_status_map.contains_key(slot) {
                assert(post.status_map[slot] is Clean);
                assert(post.entries[slot] is Filled);
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }
    }
    
    #[inductive(evict)]
    fn evict_inductive(pre: Self, post: Self, lbl: Label, evicted_slots: Set<Slot>) { 
        let evicted_addrs = Map::new(|slot| evicted_slots.contains(slot), |slot| pre.entries[slot].get_addr()).values();
        let updated_entries = Map::new(|slot| evicted_slots.contains(slot), |slot| Entry::Empty);
        let updated_status_map = Map::new(|slot| evicted_slots.contains(slot), |slot| Status::NotFilled);

        assert(pre.slots_hold_unique_addr());
        pre.build_lookup_map_ensures();

        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                assert(!evicted_slots.contains(s1));
                assert(!evicted_slots.contains(s2));
                assert(post.entries[s1] == pre.entries[s1]);
                assert(post.entries[s2] == pre.entries[s2]);
                assert(pre.non_empty_slot(s1));
                assert(pre.non_empty_slot(s2));
                assert(pre.entries[s1].get_addr() != pre.entries[s2].get_addr());
            }
        }

        Self::union_prefer_right_preserves_dom_entry(pre.entries, updated_entries);
        Self::union_prefer_right_preserves_dom_status(pre.status_map, updated_status_map);
        Self::remove_keys_dom(pre.lookup_map, evicted_addrs);
        assert(post.entries.dom() =~= pre.entries.dom());
        assert(post.status_map.dom() =~= pre.status_map.dom());
        assert(post.status_map.dom() =~= post.entries.dom());

        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            if evicted_slots.contains(slot) {
                assert(post.status_map[slot] is NotFilled);
                assert(!(post.entries[slot] is Filled));
            } else {
                assert(post.status_map[slot] == pre.status_map[slot]);
                assert(post.entries[slot] == pre.entries[slot]);
            }
        }

        assert(post.build_lookup_map_props(post.lookup_map)) by {
            assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) implies {
                let slot = post.lookup_map[addr];
                &&& post.entries.contains_key(slot)
                &&& !(post.entries[slot] is Empty)
                &&& post.entries[slot].get_addr() == addr
            } by {
                assert(pre.lookup_map.contains_key(addr));
                let slot = pre.lookup_map[addr];
                assert(post.lookup_map[addr] == slot);
                assert(!evicted_addrs.contains(addr));
                assert(!evicted_slots.contains(slot)) by {
                    if evicted_slots.contains(slot) {
                        assert(pre.entries[slot].get_addr() == addr);
                        let evicted_map = Map::new(
                            |s: Slot| evicted_slots.contains(s),
                            |s: Slot| pre.entries[s].get_addr(),
                        );
                        assert(evicted_map.contains_key(slot));
                        assert(evicted_map[slot] == pre.entries[slot].get_addr());
                        assert(evicted_map.contains_value(pre.entries[slot].get_addr()));
                        assert(evicted_addrs.contains(pre.entries[slot].get_addr()));
                        assert(evicted_addrs.contains(addr));
                    }
                }
                assert(post.entries[slot] == pre.entries[slot]);
                assert(!(post.entries[slot] is Empty));
                assert(post.entries[slot].get_addr() == addr);
            }

            assert forall |slot| #[trigger] post.entries.contains_key(slot) && !(post.entries[slot] is Empty) implies {
                let addr = post.entries[slot].get_addr();
                post.lookup_map.contains_key(addr) && post.lookup_map[addr] == slot
            } by {
                let addr = post.entries[slot].get_addr();
                assert(!evicted_slots.contains(slot));
                assert(post.entries[slot] == pre.entries[slot]);
                assert(pre.lookup_map.contains_key(addr));
                assert(pre.lookup_map[addr] == slot);
                assert(!evicted_addrs.contains(addr)) by {
                    if evicted_addrs.contains(addr) {
                        let s = choose |s: Slot| evicted_slots.contains(s) && pre.entries[s].get_addr() == addr;
                        assert(pre.non_empty_slot(s));
                        assert(pre.non_empty_slot(slot));
                        assert(pre.entries[s].get_addr() == pre.entries[slot].get_addr());
                        assert(s == slot);
                        assert(false);
                    }
                }
                assert(post.lookup_map.contains_key(addr));
                assert(post.lookup_map[addr] == slot);
            }

            assert(post.lookup_map.is_injective()) by {
                assert forall |a1: Address, a2: Address|
                    post.lookup_map.contains_key(a1)
                    && post.lookup_map.contains_key(a2)
                    && a1 != a2
                    implies #[trigger] post.lookup_map[a1] != #[trigger] post.lookup_map[a2]
                by {
                    let s1 = post.lookup_map[a1];
                    let s2 = post.lookup_map[a2];
                    if s1 == s2 {
                        assert(post.entries[s1].get_addr() == a1);
                        assert(post.entries[s2].get_addr() == a2);
                        assert(a1 == a2);
                        assert(false);
                    }
                }
            }
        }
        post.build_lookup_map_is_unique(post.lookup_map);
    }
    
    #[inductive(evictable)]
    fn evictable_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, slots: nat) { 
        assert(post.entries == Map::new(|i: Slot| i < slots , |i| Entry::Empty));
        assert(post.status_map == Map::new(|i: Slot| i < slots , |i| Status::NotFilled));
        assert(post.lookup_map == Map::<Address, Slot>::empty());
        assert(post.slots_hold_unique_addr()) by {
            assert forall |s1, s2| #[trigger] post.non_empty_slot(s1)
                && #[trigger] post.non_empty_slot(s2) && s1 != s2
                implies post.entries[s1].get_addr() != post.entries[s2].get_addr()
            by {
                assert(!(post.entries[s1] is Empty));
                assert(post.entries[s1] == Entry::Empty);
                assert(false);
            }
        }
        assert(post.status_map.dom() =~= post.entries.dom());
        assert(post.lookup_map == post.build_lookup_map()) by {
            reveal(Cache::State::build_lookup_map);
            assert(post.build_lookup_map() == Map::<Address, Slot>::empty());
        }
        assert forall |slot| #[trigger] post.status_map.contains_key(slot)
            implies ((post.status_map[slot] is NotFilled) <==> !(post.entries[slot] is Filled))
        by {
            assert(post.status_map[slot] is NotFilled);
            assert(!(post.entries[slot] is Filled));
        }
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires Self::next(pre, post, lbl), pre.inv()
        ensures post.inv()
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step| Cache::State::next_by(pre, post, lbl, step);
        match step {
            Step::reserve(new_slots_mapping) => {
                Self::reserve_inductive(pre, post, lbl, new_slots_mapping);
            }
            Step::load_initiate(new_slots_mapping) => {
                Self::load_initiate_inductive(pre, post, lbl, new_slots_mapping);
            }
            Step::load_complete() => {
                Self::load_complete_inductive(pre, post, lbl);
            }
            Step::access() => {
                Self::access_inductive(pre, post, lbl);
            }
            Step::writeback_initiate() => {
                Self::writeback_initiate_inductive(pre, post, lbl);
            }
            Step::writeback_complete() => {
                Self::writeback_complete_inductive(pre, post, lbl);
            }
            Step::evict(evicted_slots) => {
                Self::evict_inductive(pre, post, lbl, evicted_slots);
            }
            Step::evictable() => {
                Self::evictable_inductive(pre, post, lbl);
            }
            Step::noop() => {
                Self::noop_inductive(pre, post, lbl);
            }
            _ => {
                assert(false);
            }
        }
    }
    
    /// When reads and writes are both empty, the access transition is a no-op.
    /// This lemma witnesses that State::next holds for any state with itself.
    pub proof fn access_empty_is_noop(s: State)
    ensures
        State::next(s, s, Label::Access{reads: Map::empty(), writes: Map::empty()})
    {
        reveal(State::next_by);
        reveal(State::next);
        
        let lbl = Label::Access{reads: Map::<Address, RawPage>::empty(), writes: Map::<Address, RawPage>::empty()};
        let write_slots = s.lookup_map.restrict(lbl->writes.dom()).values();

        let updated_entries: Map<Slot, Entry> = Map::new(
            |slot: Slot| write_slots.contains(slot),
            |slot: Slot| Entry::Filled{
                addr: s.entries[slot].get_addr(), 
                data: lbl->writes[s.entries[slot].get_addr()]
            });
        assert( s.entries.union_prefer_right(updated_entries) =~= s.entries );  // extn

        let updated_status_map: Map<Slot, Status> = Map::new(
            |slot: Slot| write_slots.contains(slot),
            |slot: Slot| Status::Dirty
        );
        assert( s.status_map.union_prefer_right(updated_status_map) =~= s.status_map ); // extn
        
        // Witness the step
        assert( State::next_by(s, s, lbl, Step::access()) ); // step witness
    }
}}

pub mod State {
    use super::*;

    pub type State = Cache::State;
    pub type Label = Cache::Label;

    pub open spec fn inv(s: State) -> bool {
        s.inv()
    }

    pub proof fn inv_next(pre: State, post: State, lbl: Label)
        requires
            Cache::State::next(pre, post, lbl),
            pre.inv(),
        ensures
            post.inv(),
    {
        Cache::State::inv_next(pre, post, lbl);
    }

    pub proof fn access_empty_is_noop(s: State)
        ensures
            Cache::State::next(
                s,
                s,
                Cache::Label::Access{reads: Map::empty(), writes: Map::empty()},
            ),
    {
        Cache::State::access_empty_is_noop(s);
    }
}

// TODO(verus): Surely this should be constructed by the macros.
pub open spec fn cache_functional_new(slots: nat) -> Cache::State
{
    Cache::State {
        entries: Map::new(|i: Slot| i < slots , |i| Entry::Empty),
        status_map: Map::new(|i: Slot| i < slots , |i| Status::NotFilled),
        lookup_map: Map::empty(),
    }
}
} // end of !verus
