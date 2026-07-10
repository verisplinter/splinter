// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::disk::GenericDisk_v::{AU, Address, page_count};

verus! {

pub struct PageAllocator {
    pub allocated: Set<Address>,
    pub au: AU,
}

impl PageAllocator {
    pub open spec(checked) fn new(au: AU) -> Self {
        Self{allocated: Set::empty(), au}
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& (forall |addr| #![auto] self.allocated.contains(addr) ==> addr.wf())
        &&& (forall |addr| #![auto] self.allocated.contains(addr) ==> addr.au == self.au)
    }

    pub open spec(checked) fn is_free_addr(self, addr: Address) -> bool {
        &&& addr.wf()
        &&& addr.au == self.au
        &&& !self.allocated.contains(addr)
    }

    /// Compatibility name: allocate pages into this AU.
    pub open spec(checked) fn reserve(self, addrs: Set<Address>) -> (out: Self)
    recommends
        self.wf(),
        forall |addr| addrs.contains(addr) ==> self.is_free_addr(addr),
    // ensures out.wf()
    {
        Self{allocated: self.allocated + addrs, ..self}
    }

    pub open spec(checked) fn free(self, addrs: Set<Address>) -> (out: Self)
    recommends
            self.wf(),
            addrs.subset_of(self.allocated),  // ensures out.wf()
    {
        Self{allocated: self.allocated.difference(addrs), au: self.au}
    }

    pub open spec(checked) fn has_no_allocated_pages(self) -> bool {
        &&& self.allocated == Set::<Address>::empty()
    }

    pub open spec(checked) fn all_pages_allocated(self) -> bool {
        forall |addr: Address| #![auto] addr.wf() && addr.au == self.au 
            ==> self.allocated.contains(addr)
    }

    pub open spec(checked) fn all_pages_free(self) -> bool {
        self.has_no_allocated_pages()
    }
}

pub struct MiniAllocator {
    pub allocs: Map<AU, PageAllocator>,
    pub curr: Option<AU>,
}

impl MiniAllocator {
    pub open spec(checked) fn empty() -> Self {
        Self{allocs: Map::empty(), curr: None}
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& forall |au| #[trigger] self.allocs.contains_key(au) ==> self.allocs[au].wf() && self.allocs[au].au == au
        &&& self.curr is Some ==> self.allocs.contains_key(self.curr.unwrap())
    }

    pub open spec(checked) fn add_aus(self, aus: Set<AU>) -> Self
        recommends
            self.wf(),  // ensures out.wf()
    {
        let new_allocs = Map::new(
            |au| (aus+self.allocs.dom()).contains(au),
            |au| if self.allocs.contains_key(au) { self.allocs[au] }
                else { PageAllocator::new(au) });
        Self{allocs: new_allocs, ..self}
    }

    // Mini allocator tracks pages allocated out of each owned AU. An AU with no
    // allocated pages can be removed from the mini allocator.
    pub open spec(checked) fn can_remove(self, au: AU) -> bool {
        &&& self.allocs.contains_key(au)
        &&& self.allocs[au].has_no_allocated_pages()
    }

    pub open spec(checked) fn can_allocate(self, addr: Address) -> bool
    {
        &&& self.allocs.contains_key(addr.au)
        &&& self.allocs[addr.au].is_free_addr(addr)
    }

    pub open spec(checked) fn allocate(self, addr: Address) -> Self
        recommends
            self.wf(),
            self.can_allocate(addr),  // ensures out.wf()
    {
        let result = self.allocs[addr.au].reserve(set![addr]);
        let new_curr = if result.all_pages_allocated() { None } else { Some(addr.au) };
        Self{ allocs: self.allocs.insert(addr.au, result), curr: new_curr }
    }

    pub proof fn allocate_allocated_aus(self, addr: Address)
        requires
            self.wf(),
            self.can_allocate(addr),
        ensures
            self.allocate(addr).allocated_aus() =~= self.allocated_aus().insert(addr.au),
    {
        let post = self.allocate(addr);
        assert forall |au: AU| #[trigger] post.allocated_aus().contains(au)
            <==> self.allocated_aus().insert(addr.au).contains(au) by {
            if au == addr.au {
                assert(post.allocs[au].allocated.contains(addr));
                assert(post.allocs[au].allocated != Set::<Address>::empty());
            } else {
                assert(post.allocs.contains_key(au) == self.allocs.contains_key(au));
                if post.allocs.contains_key(au) {
                    assert(post.allocs[au] == self.allocs[au]);
                }
            }
        }
    }

    pub proof fn allocate_can_allocate_subset(self, allocated: Address, addr: Address)
        requires
            self.wf(),
            self.can_allocate(allocated),
            self.allocate(allocated).can_allocate(addr),
        ensures
            self.can_allocate(addr),
    {
        let after = self.allocate(allocated);
        assert(after.allocs.contains_key(addr.au));
        if addr.au == allocated.au {
            assert(self.allocs.contains_key(addr.au));
            assert(after.allocs[addr.au]
                == self.allocs[addr.au].reserve(set![allocated]));
            assert(after.allocs[addr.au].is_free_addr(addr));
            assert(addr.wf());
            assert(addr.au == self.allocs[addr.au].au);
            assert(!after.allocs[addr.au].allocated.contains(addr));
            assert(!self.allocs[addr.au].allocated.contains(addr));
            assert(self.allocs[addr.au].is_free_addr(addr));
        } else {
            assert(after.allocs[addr.au] == self.allocs[addr.au]);
            assert(self.allocs.contains_key(addr.au));
            assert(after.allocs[addr.au].is_free_addr(addr));
            assert(self.allocs[addr.au].is_free_addr(addr));
        }
        assert(self.can_allocate(addr));
    }

    pub open spec/*(checked)*/ fn prune(self, aus: Set<AU>) -> Self
    recommends
        self.wf(),
    {
        // let new_allocs = Map::new(
        //     |au| self.allocs.contains_key(au) && !aus.contains(au),
        //     |au| self.allocs[au]);

        let new_allocs = self.allocs.remove_keys(aus);
        let new_curr = if self.curr is Some && aus.contains(self.curr.unwrap()) 
                        { None } else { self.curr };

        Self{allocs: new_allocs, curr: new_curr}
    }

    pub proof fn prune_allocated_aus_empty(self)
        requires
            self.wf(),
        ensures
            self.prune(self.allocated_aus()).allocated_aus() =~= Set::<AU>::empty(),
    {
        let post = self.prune(self.allocated_aus());
        assert forall |au: AU| #[trigger] post.allocated_aus().contains(au)
            implies false by {
            assert(post.allocs.contains_key(au));
            assert(self.allocs.contains_key(au));
            assert(post.allocs[au] == self.allocs[au]);
            assert(!post.allocs[au].has_no_allocated_pages());
            assert(self.allocated_aus().contains(au));
            assert(!post.allocs.contains_key(au));
        }
    }

    pub proof fn prune_preserves_wf(self, aus: Set<AU>)
        requires
            self.wf(),
        ensures
            self.prune(aus).wf(),
            self.prune(aus).all_aus() == self.all_aus().difference(aus),
    {
        let post = self.prune(aus);
        assert(post.all_aus() =~= self.all_aus().difference(aus)) by {
            assert forall |au: AU| #[trigger] post.all_aus().contains(au)
                <==> self.all_aus().difference(aus).contains(au) by { }
        }
        assert forall |au: AU| #[trigger] post.allocs.contains_key(au)
            implies post.allocs[au].wf() && post.allocs[au].au == au by {
            assert(self.allocs.contains_key(au));
            assert(!aus.contains(au));
        }
        if post.curr is Some {
            assert(self.curr is Some);
            assert(post.curr.unwrap() == self.curr.unwrap());
            assert(!aus.contains(post.curr.unwrap()));
            assert(self.allocs.contains_key(post.curr.unwrap()));
            assert(post.allocs.contains_key(post.curr.unwrap()));
        }
        assert(post.wf());
    }

    pub open spec fn page_is_allocated(self, addr: Address) -> bool
    {
        &&& self.allocs.contains_key(addr.au)
        &&& self.allocs[addr.au].allocated.contains(addr)
    }

    pub open spec fn allocated_aus(self) -> Set<AU>
    {
        Set::new(|au| self.allocs.contains_key(au) && !self.allocs[au].has_no_allocated_pages())
    }

    pub open spec fn removable_aus(self) -> Set<AU>
    {
        Set::new(|au| self.can_remove(au))
    }

    pub open spec fn all_aus(self) -> Set<AU>
    {
        self.allocs.dom()
    }

}

}  // end verus!
