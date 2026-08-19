// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_sets_equal;
use vstd::assert_maps_equal;

use crate::allocation_layer::MiniAllocator_v::{
    MiniAllocator as SpecMiniAllocator, PageAllocator as SpecMiniPageAllocator,
};
use crate::disk::GenericDisk_v::{AU, Address, page_count};
use crate::implementation::AuPoolImpl_v::{iau_vec_set, AuAllocation, AuPoolImpl};
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::implementation::PageAllocator_v::PageAllocator;
use crate::spec::ImplDisk_t::{IAddress, IAU, IPage};

verus! {

proof fn au_allocation_vec_set_matches(allocation: AuAllocation, total_aus: IAU)
    requires
        allocation.wf(total_aus),
    ensures
        iau_vec_set(allocation.aus@) =~= allocation.as_set(),
{
    assert forall |au: AU| #[trigger] iau_vec_set(allocation.aus@).contains(au)
        implies allocation.as_set().contains(au) by {
        let idx = choose |i: int| 0 <= i < allocation.aus@.len()
            && #[trigger] (allocation.aus@[i] as nat) == au;
        assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
        assert((allocation.aus@[idx] as nat) == (allocation.run.start as nat) + (idx as nat));
        assert((allocation.run.start as nat) <= au);
        assert(au < (allocation.run.end as nat));
        assert(allocation.run.contains_au(au));
    }
    assert forall |au: AU| #[trigger] allocation.as_set().contains(au)
        implies iau_vec_set(allocation.aus@).contains(au) by {
        assert(allocation.run.contains_au(au));
        assert((allocation.run.start as nat) <= au);
        assert(au < (allocation.run.end as nat));
        let idx = (au - (allocation.run.start as nat)) as int;
        assert(0 <= idx);
        assert(idx < allocation.aus@.len());
        assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
        assert((allocation.aus@[idx] as nat) == au);
    }
}

proof fn au_allocation_vec_unique(allocation: AuAllocation, total_aus: IAU)
    requires
        allocation.wf(total_aus),
    ensures
        MiniAllocatorImpl::iau_seq_unique(allocation.aus@),
{
    assert forall |i: int, j: int| 0 <= i < allocation.aus@.len()
        && 0 <= j < allocation.aus@.len()
        && #[trigger] allocation.aus@[i] == #[trigger] allocation.aus@[j]
        implies i == j by {
        assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
        assert((allocation.aus@[i] as nat) == (allocation.run.start as nat) + (i as nat));
        assert((allocation.aus@[j] as nat) == (allocation.run.start as nat) + (j as nat));
    }
}

fn iau_vec_contains(aus: &Vec<IAU>, target: IAU) -> (out: bool)
    ensures
        out <==> aus@.contains(target),
{
    let mut idx: usize = 0;
    while idx < aus.len()
        invariant
            idx <= aus.len(),
            forall |i: int| 0 <= i < idx ==> #[trigger] aus@[i] != target,
        decreases aus.len() - idx,
    {
        if aus[idx] == target {
            return true;
        }
        idx = idx + 1;
    }
    false
}

pub struct MiniAllocatorImpl {
    pub allocators: Vec<PageAllocator>,
    pub curr: Option<IAU>,
    pub free_au_threshold: IAU,
}

impl MiniAllocatorImpl {
    pub open spec fn allocators_wf(allocators: Seq<PageAllocator>) -> bool
    {
        forall |i: int| 0 <= i < allocators.len() ==> #[trigger] allocators[i].wf()
    }

    pub open spec fn allocators_unique(allocators: Seq<PageAllocator>) -> bool
    {
        forall |i: int, j: int| 0 <= i < allocators.len() && 0 <= j < allocators.len()
            && #[trigger] allocators[i].alloc_au_nat() == #[trigger] allocators[j].alloc_au_nat()
            ==> i == j
    }

    pub open spec fn allocators_au_set(allocators: Seq<PageAllocator>) -> Set<AU>
    {
        Set::new(|au: AU| exists |i: int|
            0 <= i < allocators.len() && #[trigger] allocators[i].alloc_au_nat() == au)
    }

    pub open spec fn allocators_bounded(allocators: Seq<PageAllocator>, total_aus: IAU) -> bool
    {
        forall |i: int| 0 <= i < allocators.len() ==> {
            &&& 0 < #[trigger] allocators[i].alloc_au_nat()
            &&& allocators[i].alloc_au_nat() < (total_aus as nat)
        }
    }

    pub open spec fn bounded(&self, total_aus: IAU) -> bool
    {
        Self::allocators_bounded(self.allocators@, total_aus)
    }

    pub proof fn owned_au_bounded(&self, total_aus: IAU, au: AU)
        requires
            self.bounded(total_aus),
            self.i().all_aus().contains(au),
        ensures
            0 < au,
            au < total_aus as nat,
    {
        Self::allocators_i_dom(self.allocators@);
        assert(Self::allocators_au_set(self.allocators@).contains(au));
        let idx = choose |idx: int|
            0 <= idx < self.allocators@.len()
                && #[trigger] self.allocators@[idx].alloc_au_nat() == au;
        assert(Self::allocators_bounded(
            self.allocators@,
            total_aus,
        ));
    }

    pub proof fn all_aus_match(&self)
        ensures
            Self::allocators_au_set(self.allocators@)
                =~= self.i().all_aus(),
    {
        Self::allocators_i_dom(self.allocators@);
    }

    pub proof fn active_allocator_bounded(&self, total_aus: IAU)
        requires
            self.allocation_ready(),
            Self::allocators_bounded(self.allocators@, total_aus),
        ensures
            0 < self.alloc_au_nat(),
            self.alloc_au_nat() < (total_aus as nat),
    {
        reveal(MiniAllocatorImpl::active_allocator);
        reveal(MiniAllocatorImpl::alloc_au_nat);
        let idx = self.allocators@.len() - 1;
        assert(0 <= idx < self.allocators@.len());
        assert(self.active_allocator() == self.allocators@[idx]);
        assert(self.alloc_au_nat() == self.allocators@[idx].alloc_au_nat());
        assert(0 < self.allocators@[idx].alloc_au_nat());
        assert(self.allocators@[idx].alloc_au_nat() < (total_aus as nat));
    }

    pub proof fn allocated_aus_bounded(&self, total_aus: IAU)
        requires
            self.bounded(total_aus),
        ensures
            forall |au: AU| #[trigger] self.i().allocated_aus().contains(au)
                ==> 0 < au < (total_aus as nat),
    {
        assert forall |au: AU| #[trigger] self.i().allocated_aus().contains(au)
            implies 0 < au < (total_aus as nat) by {
            assert(self.i().allocs.contains_key(au));
            let idx = choose |idx: int| 0 <= idx < self.allocators@.len()
                && #[trigger] self.allocators@[idx].alloc_au_nat() == au;
            assert(0 < self.allocators@[idx].alloc_au_nat());
            assert(self.allocators@[idx].alloc_au_nat() < (total_aus as nat));
        }
    }

    pub proof fn page_allocator_prefix_all_pages_allocated(
        allocator: PageAllocator,
        disk_page_count: IPage,
    )
        requires
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == page_count(),
        ensures
            Self::page_allocator_i(allocator).all_pages_allocated()
                <==> (disk_page_count as nat) <= (allocator.next_page() as nat),
    {
        if (disk_page_count as nat) <= (allocator.next_page() as nat) {
            assert forall |addr: Address|
                addr.wf() && addr.au == allocator.alloc_au_nat()
                implies #[trigger] (Self::page_allocator_i(allocator).allocated
                    + Self::page_allocator_i(allocator).allocated).contains(addr) by {
                assert(addr.page < page_count());
                assert(addr.page < (disk_page_count as nat));
                assert(addr.page < allocator.next_page() as nat);
                assert(Self::page_allocator_allocated(allocator).contains(addr));
                assert(Self::page_allocator_i(allocator).allocated.contains(addr));
            }
            assert(Self::page_allocator_i(allocator).all_pages_allocated());
        } else {
            let addr = Address{au: allocator.alloc_au_nat(), page: allocator.next_page() as nat};
            assert(addr.wf()) by {
                assert(addr.page < page_count());
            }
            assert(!Self::page_allocator_i(allocator).allocated.contains(addr)) by {
                if Self::page_allocator_i(allocator).allocated.contains(addr) {
                    assert(addr.page < allocator.next_page() as nat);
                    assert(false);
                }
            }
            assert(!Self::page_allocator_i(allocator).allocated.contains(addr));
            assert(!(Self::page_allocator_i(allocator).allocated
                + Self::page_allocator_i(allocator).allocated).contains(addr));
            assert(!Self::page_allocator_i(allocator).all_pages_allocated());
        }
    }

    pub proof fn prove_active_next_addr_can_allocate(
        &self,
        disk_au_count: IAU,
        disk_page_count: IPage,
    )
        requires
            self.allocation_ready(),
            Self::allocators_unique(self.allocators@),
            Self::allocators_bounded(self.allocators@, disk_au_count),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == page_count(),
            (self.next_page() as nat) < (disk_page_count as nat),
        ensures
            self.i().can_allocate(Address{
                au: self.alloc_au_nat(),
                page: self.next_page() as nat,
            }),
    {
        reveal(MiniAllocatorImpl::active_allocator);
        reveal(MiniAllocatorImpl::alloc_au_nat);
        reveal(MiniAllocatorImpl::next_page);
        let idx = self.allocators@.len() - 1;
        let addr = Address{au: self.alloc_au_nat(), page: self.next_page() as nat};
        self.active_allocator_bounded(disk_au_count);
        assert(addr.wf()) by {
            assert(addr.page < page_count());
        }
        assert(self.i().allocs.contains_key(addr.au)) by {
            assert(self.allocators@[idx].alloc_au_nat() == addr.au);
            assert(exists |i: int| 0 <= i < self.allocators@.len()
                && #[trigger] self.allocators@[i].alloc_au_nat() == addr.au);
        }
        let chosen = choose |i: int| 0 <= i < self.allocators@.len()
            && #[trigger] self.allocators@[i].alloc_au_nat() == addr.au;
        assert(chosen == idx) by {
            assert(self.allocators@[chosen].alloc_au_nat() == self.allocators@[idx].alloc_au_nat());
            assert(Self::allocators_unique(self.allocators@));
        }
        let pa = self.i().allocs[addr.au];
        assert(pa == Self::page_allocator_i(self.active_allocator()));
        assert(pa.au == addr.au);
        assert(!pa.allocated.contains(addr));
        assert(!pa.allocated.contains(addr)) by {
            if pa.allocated.contains(addr) {
                assert(Self::page_allocator_allocated(self.active_allocator()).contains(addr));
                assert(addr.page < self.next_page() as nat);
                assert(false);
            }
        }
        assert(pa.is_free_addr(addr));
        assert(self.i().can_allocate(addr));
    }

    pub proof fn curr_none_page_zero_next_addr_all_pages_free(&self)
        requires
            self.allocation_ready(),
            Self::allocators_unique(self.allocators@),
            self.curr is None,
            self.next_addr().page == 0,
        ensures
            self.i().allocs.contains_key(self.next_addr().au),
            self.i().allocs[self.next_addr().au].all_pages_free(),
    {
        let idx = self.allocators@.len() - 1;
        let active = self.active_allocator();
        let addr = self.next_addr();
        assert(active == self.allocators@[idx]);
        assert(active.alloc_au_nat() == addr.au);
        assert(active.next_page() == 0);
        assert(self.i().allocs.contains_key(addr.au));
        let chosen = choose |i: int| 0 <= i < self.allocators@.len()
            && #[trigger] self.allocators@[i].alloc_au_nat() == addr.au;
        assert(chosen == idx) by {
            assert(self.allocators@[chosen].alloc_au_nat()
                == self.allocators@[idx].alloc_au_nat());
            assert(Self::allocators_unique(self.allocators@));
        }
        assert(self.i().allocs[addr.au] == Self::page_allocator_i(active));
        assert(Self::page_allocator_i(active).allocated =~= Set::<Address>::empty()) by {
            assert forall |a: Address|
                #[trigger] Self::page_allocator_i(active).allocated.contains(a)
                implies false by {
                assert(Self::page_allocator_allocated(active).contains(a));
                assert(a.page < active.next_page() as nat);
            }
        }
        assert(self.i().allocs[addr.au].all_pages_free());
    }

    pub proof fn active_au_allocated_if_next_page_positive(
        &self,
        disk_au_count: IAU,
        disk_page_count: IPage,
    )
        requires
            self.allocation_ready(),
            Self::allocators_unique(self.allocators@),
            self.bounded(disk_au_count),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == page_count(),
            0 < self.next_page(),
        ensures
            self.i().allocated_aus().contains(self.alloc_au_nat()),
    {
        let idx = self.allocators@.len() - 1;
        let active = self.active_allocator();
        let au = self.alloc_au_nat();
        assert(active == self.allocators@[idx]);
        assert(active.alloc_au_nat() == au);
        assert(self.i().allocs.contains_key(au));
        let chosen = choose |i: int| 0 <= i < self.allocators@.len()
            && #[trigger] self.allocators@[i].alloc_au_nat() == au;
        assert(chosen == idx) by {
            assert(Self::allocators_unique(self.allocators@));
        }
        let addr = Address{au, page: 0};
        assert(addr.wf()) by {
            self.active_allocator_bounded(disk_au_count);
            assert(0 < page_count());
        }
        assert(Self::page_allocator_i(active).allocated.contains(addr));
        assert(!self.i().allocs[au].has_no_allocated_pages());
    }

    pub open spec fn iau_seq_unique(aus: Seq<IAU>) -> bool
    {
        forall |i: int, j: int| 0 <= i < aus.len() && 0 <= j < aus.len()
            && #[trigger] aus[i] == #[trigger] aus[j] ==> i == j
    }

    pub open spec fn wf(&self) -> bool
    {
        &&& Self::allocators_wf(self.allocators@)
        &&& self.curr is Some ==> exists |i: int|
            0 <= i < self.allocators@.len()
                && #[trigger] self.allocators@[i].alloc_au_nat() == self.curr.unwrap() as nat
        &&& self.curr is Some ==> self.i().allocs.contains_key(self.curr.unwrap() as nat)
    }

    pub proof fn prove_curr_in_i_allocs(&self)
        requires
            Self::allocators_wf(self.allocators@),
            self.curr is Some ==> exists |i: int|
                0 <= i < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat() == self.curr.unwrap() as nat,
        ensures
            self.curr is Some ==> self.i().allocs.contains_key(self.curr.unwrap() as nat),
    {
        if self.curr is Some {
            let curr_au = self.curr.unwrap();
            let idx = choose |i: int| 0 <= i < self.allocators@.len()
                && #[trigger] self.allocators@[i].alloc_au_nat() == curr_au as nat;
            assert(self.allocators@[idx].alloc_au_nat() == curr_au as nat);
            assert(self.i().allocs.contains_key(curr_au as nat));
        }
    }

    pub open spec fn allocation_ready(&self) -> bool
    {
        &&& self.wf()
        &&& 0 < self.allocators@.len()
    }

    pub fn is_allocation_ready(&self) -> (out: bool)
        requires
            self.wf(),
        ensures
            out == self.allocation_ready(),
    {
        self.allocators.len() > 0
    }

    pub closed spec fn active_allocator(&self) -> PageAllocator
        recommends
            self.allocation_ready(),
    {
        self.allocators@[self.allocators@.len() - 1]
    }

    pub closed spec fn alloc_au(&self) -> IAU
        recommends
            self.allocation_ready(),
    {
        self.active_allocator().alloc_au()
    }

    pub closed spec fn alloc_au_nat(&self) -> nat
        recommends
            self.allocation_ready(),
    {
        self.active_allocator().alloc_au() as nat
    }

    pub closed spec fn next_page(&self) -> IPage
        recommends
            self.allocation_ready(),
    {
        self.active_allocator().next_page()
    }

    pub closed spec fn next_addr(&self) -> Address
        recommends
            self.allocation_ready(),
    {
        Address{
            au: self.alloc_au_nat(),
            page: self.next_page() as nat,
        }
    }

    pub closed spec fn next_addr_wf(&self) -> bool
        recommends
            self.allocation_ready(),
    {
        self.active_allocator().next_addr_wf()
    }

    pub closed spec fn threshold(&self) -> IAU
    {
        self.free_au_threshold
    }

    pub open spec fn page_allocator_allocated(allocator: PageAllocator) -> Set<Address>
    {
        Set::new(|addr: Address| {
            &&& addr.wf()
            &&& addr.au == allocator.alloc_au_nat()
            &&& addr.page < allocator.next_page() as nat
        })
    }

    pub open spec fn page_allocator_i(allocator: PageAllocator) -> SpecMiniPageAllocator
    {
        SpecMiniPageAllocator {
            allocated: Self::page_allocator_allocated(allocator),
            au: allocator.alloc_au_nat(),
        }
    }

    pub open spec fn allocators_i(
        allocators: Seq<PageAllocator>,
    ) -> Map<AU, SpecMiniPageAllocator>
    {
        Map::new(
            |au: AU| exists |idx: int|
                0 <= idx < allocators.len() && allocators[idx].alloc_au_nat() == au,
            |au: AU| {
                let idx = choose |idx: int|
                    0 <= idx < allocators.len() && allocators[idx].alloc_au_nat() == au;
                Self::page_allocator_i(allocators[idx])
            },
        )
    }

    pub open spec fn i(&self) -> SpecMiniAllocator
    {
        let allocs = Self::allocators_i(self.allocators@);
        let curr = if self.curr is Some { Some(self.curr.unwrap() as nat) } else { None };
        SpecMiniAllocator { allocs, curr }
    }

    pub fn empty(free_au_threshold: IAU) -> (out: Self)
        ensures
            out.wf(),
            !out.allocation_ready(),
            out.threshold() == free_au_threshold,
            out.allocators@.len() == 0,
            Self::allocators_unique(out.allocators@),
            out.i() == SpecMiniAllocator::empty(),
            out.i().allocated_aus() == Set::<AU>::empty(),
    {
        let out = Self { allocators: Vec::new(), curr: None, free_au_threshold };
        proof {
            assert(out.i().allocs =~= Map::<AU, SpecMiniPageAllocator>::empty());
            assert(out.i().curr is None);
            assert(out.i() == SpecMiniAllocator::empty());
            assert(out.i().allocated_aus() =~= Set::<AU>::empty()) by {
                assert forall |au: AU| #[trigger] out.i().allocated_aus().contains(au)
                    implies false by {
                    assert(out.i().allocs.contains_key(au));
                }
            }
        }
        out
    }

    pub proof fn not_allocation_ready_implies_allocated_aus_empty(&self)
        requires
            self.wf(),
            !self.allocation_ready(),
        ensures
            self.i().allocated_aus() == Set::<AU>::empty(),
    {
        assert(!(0 < self.allocators@.len()));
        assert(self.allocators@.len() == 0);
        assert(self.i().allocs =~= Map::<AU, SpecMiniPageAllocator>::empty()) by {
            assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                implies false by {
                let idx = choose |i: int| 0 <= i < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                assert(false);
            }
        }
        assert(self.i().allocated_aus() =~= Set::<AU>::empty()) by {
            assert forall |au: AU| #[trigger] self.i().allocated_aus().contains(au)
                implies false by {
                assert(self.i().allocs.contains_key(au));
            }
        }
    }

    pub proof fn empty_view_implies_no_allocators(&self)
        requires
            self.i() == SpecMiniAllocator::empty(),
        ensures
            self.allocators@.len() == 0,
            Self::allocators_unique(self.allocators@),
            Self::allocators_au_set(self.allocators@) =~= Set::<AU>::empty(),
    {
        if self.allocators@.len() > 0 {
            let au = self.allocators@[0].alloc_au_nat();
            assert(self.i().allocs.contains_key(au)) by {
                assert(exists |idx: int|
                    0 <= idx < self.allocators@.len()
                        && #[trigger] self.allocators@[idx].alloc_au_nat() == au);
            }
            assert(SpecMiniAllocator::empty().allocs == Map::<AU, SpecMiniPageAllocator>::empty());
            assert(false);
        }
        assert(Self::allocators_unique(self.allocators@)) by {
            assert forall |i: int, j: int| {
                &&& 0 <= i < self.allocators@.len()
                &&& 0 <= j < self.allocators@.len()
                &&& #[trigger] self.allocators@[i].alloc_au_nat()
                    == #[trigger] self.allocators@[j].alloc_au_nat()
            } implies i == j by {
                assert(false);
            }
        }
        assert_sets_equal!(
            Self::allocators_au_set(self.allocators@),
            Set::<AU>::empty(),
            au => {
                if Self::allocators_au_set(self.allocators@).contains(au) {
                    let idx = choose |idx: int|
                        0 <= idx < self.allocators@.len()
                            && #[trigger] self.allocators@[idx].alloc_au_nat() == au;
                    assert(false);
                }
            }
        );
    }

    pub fn new(alloc_au: IAU, start_page: IPage, free_au_threshold: IAU) -> (out: Self)
        ensures
            out.wf(),
            out.allocation_ready(),
            Self::allocators_unique(out.allocators@),
            out.alloc_au() == alloc_au,
            out.alloc_au_nat() == alloc_au as nat,
            out.next_page() == start_page,
            out.threshold() == free_au_threshold,
    {
        let mut allocators = Vec::<PageAllocator>::new();
        allocators.push(PageAllocator::new(alloc_au, start_page));
        let out = Self { allocators, curr: Some(alloc_au), free_au_threshold };
        proof {
            assert(out.allocators@.len() == 1);
            assert(out.allocators@[0].wf());
            out.prove_curr_in_i_allocs();
            assert(out.wf());
            assert(Self::allocators_unique(out.allocators@)) by {
                assert forall |i: int, j: int| 0 <= i < out.allocators@.len()
                    && 0 <= j < out.allocators@.len()
                    && #[trigger] out.allocators@[i].alloc_au_nat()
                        == #[trigger] out.allocators@[j].alloc_au_nat()
                    implies i == j by {
                    assert(out.allocators@.len() == 1);
                }
            }
            assert(out.active_allocator().alloc_au() == alloc_au);
            assert(out.active_allocator().next_page() == start_page);
        }
        out
    }

    pub fn clone_checked(&self) -> (out: Self)
        requires
            self.wf(),
        ensures
            out.wf(),
            out.allocators@ == self.allocators@,
            out.curr == self.curr,
            out.threshold() == self.threshold(),
            out.i() == self.i(),
            out.allocation_ready() == self.allocation_ready(),
            Self::allocators_unique(out.allocators@)
                == Self::allocators_unique(self.allocators@),
            forall |total_aus: IAU| out.bounded(total_aus)
                == self.bounded(total_aus),
    {
        let mut allocators = Vec::<PageAllocator>::new();
        let mut idx = 0usize;
        while idx < self.allocators.len()
            invariant
                idx <= self.allocators.len(),
                allocators@ == self.allocators@.take(idx as int),
            decreases self.allocators.len() - idx,
        {
            let allocator = PageAllocator::new(
                self.allocators[idx].au,
                self.allocators[idx].next_page,
            );
            proof {
                assert(allocator == self.allocators@[idx as int]);
            }
            allocators.push(allocator);
            idx += 1;
        }
        let out = Self {
            allocators,
            curr: self.curr,
            free_au_threshold: self.free_au_threshold,
        };
        proof {
            assert(out.allocators@ == self.allocators@);
            assert(out.wf());
        }
        out
    }

    pub fn reset_threshold(&mut self, free_au_threshold: IAU)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@)
                == Self::allocators_unique(old(self).allocators@),
            self.threshold() == free_au_threshold,
            self.allocation_ready() == old(self).allocation_ready(),
            old(self).allocation_ready() ==> self.alloc_au() == old(self).alloc_au(),
            old(self).allocation_ready() ==> self.alloc_au_nat() == old(self).alloc_au_nat(),
            old(self).allocation_ready() ==> self.next_page() == old(self).next_page(),
    {
        self.free_au_threshold = free_au_threshold;
    }

    pub fn free_au_count(&self) -> (out: IAU)
        requires
            self.wf(),
    {
        let mut idx: usize = 0;
        let mut count: IAU = 0;
        while idx < self.allocators.len()
            invariant
                self.wf(),
                idx <= self.allocators.len(),
            decreases self.allocators.len() - idx
        {
            let addr = self.allocators[idx].peek_next_addr();
            if addr.page == 0 {
                if count == u32::MAX {
                    convert_overflow_into_liveness_failure();
                }
                count = count + 1;
            }
            idx = idx + 1;
        }
        count
    }

    pub fn free_aus_below_threshold(&self) -> (out: bool)
        requires
            self.wf(),
    {
        self.free_au_count() < self.free_au_threshold
    }

    pub fn all_aus_vec(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
            Self::allocators_unique(self.allocators@),
        ensures
            Self::iau_seq_unique(out@),
            iau_vec_set(out@) =~= self.i().all_aus(),
            out@.len() == self.allocators@.len(),
    {
        let mut out = Vec::new();
        let mut idx = 0usize;
        while idx < self.allocators.len()
            invariant
                idx <= self.allocators.len(),
                out@.len() == idx,
                forall |i: int| 0 <= i < idx ==> {
                    &&& out@[i] == self.allocators@[i].au
                    &&& out@[i] as nat
                        == self.allocators@[i].alloc_au_nat()
                },
                Self::iau_seq_unique(out@),
            decreases self.allocators.len() - idx,
        {
            let au = self.allocators[idx].au;
            proof {
                assert forall |i: int| 0 <= i < out@.len()
                    implies #[trigger] out@[i] != au by {
                    assert(self.allocators@[i].alloc_au_nat()
                        != self.allocators@[idx as int].alloc_au_nat());
                }
            }
            out.push(au);
            idx += 1;
        }
        proof {
            assert(Self::iau_seq_unique(out@));
            Self::allocators_i_dom(self.allocators@);
            assert(iau_vec_set(out@) =~= self.i().all_aus()) by {
                assert forall |au: AU|
                    #[trigger] iau_vec_set(out@).contains(au)
                    == self.i().all_aus().contains(au) by {
                    if iau_vec_set(out@).contains(au) {
                        let i = choose |i: int| 0 <= i < out@.len()
                            && #[trigger] out@[i] as nat == au;
                        assert(self.allocators@[i].alloc_au_nat() == au);
                        assert(self.i().allocs.contains_key(au));
                    }
                    if self.i().all_aus().contains(au) {
                        assert(self.i().allocs.contains_key(au));
                        let i = choose |i: int|
                            0 <= i < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat()
                                == au;
                        assert(out@[i] as nat == au);
                    }
                }
            }
        }
        out
    }

    pub open spec fn retained_prefix(
        allocators: Seq<PageAllocator>,
        count: nat,
    ) -> Seq<PageAllocator>
        recommends count <= allocators.len(),
        decreases count,
    {
        if count == 0 {
            seq![]
        } else {
            let prefix = Self::retained_prefix(allocators, (count - 1) as nat);
            let allocator = allocators[(count - 1) as int];
            if allocator.next_page() == 0 {
                prefix.push(allocator)
            } else {
                prefix
            }
        }
    }

    pub open spec fn allocated_aus_prefix(
        allocators: Seq<PageAllocator>,
        count: nat,
    ) -> Seq<IAU>
        recommends count <= allocators.len(),
        decreases count,
    {
        if count == 0 {
            seq![]
        } else {
            let prefix = Self::allocated_aus_prefix(allocators, (count - 1) as nat);
            let allocator = allocators[(count - 1) as int];
            if allocator.next_page() > 0 {
                prefix.push(allocator.alloc_au())
            } else {
                prefix
            }
        }
    }

    pub open spec fn retained_allocated_prefix(
        allocators: Seq<PageAllocator>,
        count: nat,
    ) -> Seq<PageAllocator>
        recommends count <= allocators.len(),
        decreases count,
    {
        if count == 0 {
            seq![]
        } else {
            let prefix = Self::retained_allocated_prefix(
                allocators,
                (count - 1) as nat,
            );
            let allocator = allocators[(count - 1) as int];
            if allocator.next_page() > 0 {
                prefix.push(allocator)
            } else {
                prefix
            }
        }
    }

    pub open spec fn removable_aus_prefix(
        allocators: Seq<PageAllocator>,
        count: nat,
    ) -> Seq<IAU>
        recommends count <= allocators.len(),
        decreases count,
    {
        if count == 0 {
            seq![]
        } else {
            let prefix = Self::removable_aus_prefix(
                allocators,
                (count - 1) as nat,
            );
            let allocator = allocators[(count - 1) as int];
            if allocator.next_page() == 0 {
                prefix.push(allocator.alloc_au())
            } else {
                prefix
            }
        }
    }

    proof fn allocators_i_dom(allocators: Seq<PageAllocator>)
        ensures
            Self::allocators_i(allocators).dom() =~= Self::allocators_au_set(allocators),
    {
        assert_sets_equal!(
            Self::allocators_i(allocators).dom(),
            Self::allocators_au_set(allocators),
            au => {}
        );
    }

    proof fn iau_vec_set_push(aus: Seq<IAU>, au: IAU)
        ensures
            iau_vec_set(aus.push(au)) =~= iau_vec_set(aus).insert(au as nat),
    {
        assert_sets_equal!(iau_vec_set(aus.push(au)), iau_vec_set(aus).insert(au as nat), value => {
            if iau_vec_set(aus.push(au)).contains(value) {
                let idx = choose |i: int| 0 <= i < aus.push(au).len()
                    && #[trigger] aus.push(au)[i] as nat == value;
                if idx < aus.len() {
                    assert(aus.push(au)[idx] == aus[idx]);
                } else {
                    assert(idx == aus.len());
                    assert(value == au as nat);
                }
            }
            if iau_vec_set(aus).insert(au as nat).contains(value) {
                if iau_vec_set(aus).contains(value) {
                    let idx = choose |i: int| 0 <= i < aus.len()
                        && #[trigger] aus[i] as nat == value;
                    assert(aus.push(au)[idx] == aus[idx]);
                } else {
                    assert(value == au as nat);
                    assert(aus.push(au)[aus.len() as int] == au);
                }
            }
        });
    }

    proof fn allocators_i_push(
        allocators: Seq<PageAllocator>,
        allocator: PageAllocator,
    )
        requires
            Self::allocators_unique(allocators.push(allocator)),
        ensures
            Self::allocators_i(allocators.push(allocator))
                == Self::allocators_i(allocators).insert(
                    allocator.alloc_au_nat(),
                    Self::page_allocator_i(allocator),
                ),
    {
        let before = Self::allocators_i(allocators);
        let after = Self::allocators_i(allocators.push(allocator));
        let expected = before.insert(
            allocator.alloc_au_nat(),
            Self::page_allocator_i(allocator),
        );
        assert(Self::allocators_unique(allocators)) by {
            assert forall |i: int, j: int| 0 <= i < allocators.len()
                && 0 <= j < allocators.len()
                && #[trigger] allocators[i].alloc_au_nat()
                    == #[trigger] allocators[j].alloc_au_nat()
                implies i == j by {
                assert(allocators.push(allocator)[i] == allocators[i]);
                assert(allocators.push(allocator)[j] == allocators[j]);
                assert(Self::allocators_unique(allocators.push(allocator)));
            }
        }
        assert_maps_equal!(after, expected, au => {
            if after.contains_key(au) {
                let idx = choose |i: int| 0 <= i < allocators.push(allocator).len()
                    && #[trigger] allocators.push(allocator)[i].alloc_au_nat() == au;
                let value_idx = choose |i: int| 0 <= i < allocators.push(allocator).len()
                    && #[trigger] allocators.push(allocator)[i].alloc_au_nat() == au;
                assert(value_idx == idx) by {
                    assert(Self::allocators_unique(allocators.push(allocator)));
                }
                if au == allocator.alloc_au_nat() {
                    assert(allocators.push(allocator)[allocators.len() as int] == allocator);
                    assert(allocators.push(allocator)[idx].alloc_au_nat()
                        == allocators.push(allocator)[allocators.len() as int].alloc_au_nat());
                    assert(idx == allocators.len()) by {
                        assert(Self::allocators_unique(allocators.push(allocator)));
                    }
                    assert(after[au]
                        == Self::page_allocator_i(allocators.push(allocator)[value_idx]));
                    assert(after[au] == Self::page_allocator_i(allocator));
                } else {
                    assert(idx < allocators.len());
                    assert(before.contains_key(au));
                    let before_idx = choose |i: int| 0 <= i < allocators.len()
                        && #[trigger] allocators[i].alloc_au_nat() == au;
                    assert(allocators.push(allocator)[idx] == allocators[idx]);
                    assert(allocators.push(allocator)[before_idx] == allocators[before_idx]);
                    assert(allocators.push(allocator)[idx].alloc_au_nat()
                        == allocators.push(allocator)[before_idx].alloc_au_nat());
                    assert(idx == before_idx) by {
                        assert(Self::allocators_unique(allocators.push(allocator)));
                    }
                    assert(after[au]
                        == Self::page_allocator_i(allocators.push(allocator)[value_idx]));
                    let before_value_idx = choose |i: int| 0 <= i < allocators.len()
                        && #[trigger] allocators[i].alloc_au_nat() == au;
                    assert(before_value_idx == before_idx) by {
                        assert(Self::allocators_unique(allocators));
                    }
                    assert(before[au]
                        == Self::page_allocator_i(allocators[before_value_idx])) by {
                    }
                    assert(before[au] == Self::page_allocator_i(allocators[before_value_idx]));
                    assert(after[au] == before[au]);
                }
            }
            if expected.contains_key(au) && !after.contains_key(au) {
                if au == allocator.alloc_au_nat() {
                    assert(exists |i: int| 0 <= i < allocators.push(allocator).len()
                        && #[trigger] allocators.push(allocator)[i].alloc_au_nat() == au) by {
                        assert(allocators.push(allocator)[allocators.len() as int] == allocator);
                    }
                    assert(after.contains_key(au));
                } else {
                    assert(before.contains_key(au));
                    let idx = choose |i: int| 0 <= i < allocators.len()
                        && #[trigger] allocators[i].alloc_au_nat() == au;
                    assert(allocators.push(allocator)[idx] == allocators[idx]);
                    assert(after.contains_key(au));
                }
            }
        });
    }

    proof fn page_allocator_empty_iff_zero(allocator: PageAllocator)
        requires
            0 < page_count(),
        ensures
            Self::page_allocator_i(allocator).has_no_allocated_pages()
                <==> allocator.next_page() == 0,
    {
        if allocator.next_page() == 0 {
            assert(Self::page_allocator_i(allocator).allocated =~= Set::<Address>::empty()) by {
                assert forall |addr: Address| #[trigger]
                    Self::page_allocator_i(allocator).allocated.contains(addr)
                    implies false by {
                    assert(addr.page < allocator.next_page() as nat);
                }
            }
        } else {
            let addr = Address{au: allocator.alloc_au_nat(), page: 0};
            assert(addr.wf());
            assert(Self::page_allocator_i(allocator).allocated.contains(addr));
            assert(!Self::page_allocator_i(allocator).has_no_allocated_pages());
        }
    }

    proof fn partition_prefix_properties(
        allocators: Seq<PageAllocator>,
        count: nat,
        disk_au_count: IAU,
    )
        requires
            count <= allocators.len(),
            Self::allocators_wf(allocators),
            Self::allocators_unique(allocators),
            Self::allocators_bounded(allocators, disk_au_count),
            0 < page_count(),
        ensures
            Self::allocators_wf(Self::retained_prefix(allocators, count)),
            Self::allocators_unique(Self::retained_prefix(allocators, count)),
            Self::allocators_bounded(
                Self::retained_prefix(allocators, count),
                disk_au_count,
            ),
            Self::iau_seq_unique(Self::allocated_aus_prefix(allocators, count)),
            Self::retained_prefix(allocators, count).len() <= count,
            Self::allocated_aus_prefix(allocators, count).len() <= count,
            iau_vec_set(Self::allocated_aus_prefix(allocators, count)) =~=
                (SpecMiniAllocator{
                    allocs: Self::allocators_i(allocators.take(count as int)),
                    curr: None,
                }).allocated_aus(),
            Self::allocators_i(Self::retained_prefix(allocators, count))
                == Self::allocators_i(allocators.take(count as int)).remove_keys(
                    iau_vec_set(Self::allocated_aus_prefix(allocators, count)),
                ),
        decreases count,
    {
        if count > 0 {
            let prior_count: nat = (count - 1) as nat;
            let source_before = allocators.take(prior_count as int);
            let source = allocators.take(count as int);
            let allocator = allocators[prior_count as int];
            let kept_before = Self::retained_prefix(allocators, prior_count);
            let kept = Self::retained_prefix(allocators, count);
            let out_before = Self::allocated_aus_prefix(allocators, prior_count);
            let out = Self::allocated_aus_prefix(allocators, count);
            let removed_before = iau_vec_set(out_before);
            let removed = iau_vec_set(out);
            let source_before_i = Self::allocators_i(source_before);
            let source_i = Self::allocators_i(source);
            let kept_before_i = Self::allocators_i(kept_before);
            let kept_i = Self::allocators_i(kept);

            Self::partition_prefix_properties(allocators, prior_count, disk_au_count);
            assert(source == source_before.push(allocator));
            assert(Self::allocators_unique(source));
            Self::allocators_i_push(source_before, allocator);
            Self::page_allocator_empty_iff_zero(allocator);

            if allocator.next_page() == 0 {
                assert(kept == kept_before.push(allocator));
                assert(out == out_before);
                assert(removed == removed_before);
                assert(Self::allocators_unique(kept)) by {
                    assert forall |i: int, j: int| 0 <= i < kept.len()
                        && 0 <= j < kept.len()
                        && #[trigger] kept[i].alloc_au_nat()
                            == #[trigger] kept[j].alloc_au_nat()
                        implies i == j by {
                        if i < kept_before.len() && j < kept_before.len() {
                            assert(Self::allocators_unique(kept_before));
                        } else if i == kept_before.len() && j < kept_before.len() {
                            assert(kept_before_i.contains_key(allocator.alloc_au_nat()));
                            assert(source_before_i.contains_key(allocator.alloc_au_nat()));
                            let old_idx = choose |k: int| 0 <= k < source_before.len()
                                && #[trigger] source_before[k].alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx] == source_before[old_idx]);
                            assert(source[source_before.len() as int] == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        } else if j == kept_before.len() && i < kept_before.len() {
                            assert(kept_before_i.contains_key(allocator.alloc_au_nat()));
                            assert(source_before_i.contains_key(allocator.alloc_au_nat()));
                            let old_idx = choose |k: int| 0 <= k < source_before.len()
                                && #[trigger] source_before[k].alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx] == source_before[old_idx]);
                            assert(source[source_before.len() as int] == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        }
                    }
                }
                Self::allocators_i_push(kept_before, allocator);
                assert(kept_i == source_i.remove_keys(removed)) by {
                    assert_maps_equal!(kept_i, source_i.remove_keys(removed), au => {});
                }
                assert(removed =~= (SpecMiniAllocator{
                    allocs: source_i,
                    curr: None,
                }).allocated_aus()) by {
                    assert_sets_equal!(removed, (SpecMiniAllocator{
                        allocs: source_i,
                        curr: None,
                    }).allocated_aus(), au => {
                        if au == allocator.alloc_au_nat() {
                            assert(Self::page_allocator_i(allocator).has_no_allocated_pages());
                        }
                    });
                }
            } else {
                assert(kept == kept_before);
                assert(out == out_before.push(allocator.alloc_au()));
                Self::iau_vec_set_push(out_before, allocator.alloc_au());
                assert(removed =~= removed_before.insert(allocator.alloc_au_nat()));
                assert(Self::iau_seq_unique(out)) by {
                    assert forall |i: int, j: int| 0 <= i < out.len()
                        && 0 <= j < out.len()
                        && #[trigger] out[i] == #[trigger] out[j]
                        implies i == j by {
                        if i < out_before.len() && j < out_before.len() {
                            assert(Self::iau_seq_unique(out_before));
                        } else if i == out_before.len() && j < out_before.len() {
                            assert(removed_before.contains(allocator.alloc_au_nat()));
                            assert(source_before_i.contains_key(allocator.alloc_au_nat()));
                            let old_idx = choose |k: int| 0 <= k < source_before.len()
                                && #[trigger] source_before[k].alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx] == source_before[old_idx]);
                            assert(source[source_before.len() as int] == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        } else if j == out_before.len() && i < out_before.len() {
                            assert(removed_before.contains(allocator.alloc_au_nat()));
                            assert(source_before_i.contains_key(allocator.alloc_au_nat()));
                            let old_idx = choose |k: int| 0 <= k < source_before.len()
                                && #[trigger] source_before[k].alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx] == source_before[old_idx]);
                            assert(source[source_before.len() as int] == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        }
                    }
                }
                assert(kept_i == source_i.remove_keys(removed)) by {
                    assert_maps_equal!(kept_i, source_i.remove_keys(removed), au => {});
                }
                assert(removed =~= (SpecMiniAllocator{
                    allocs: source_i,
                    curr: None,
                }).allocated_aus()) by {
                    assert_sets_equal!(removed, (SpecMiniAllocator{
                        allocs: source_i,
                        curr: None,
                    }).allocated_aus(), au => {
                        if au == allocator.alloc_au_nat() {
                            assert(!Self::page_allocator_i(allocator).has_no_allocated_pages());
                        }
                    });
                }
            }

            assert(Self::allocators_wf(kept));
            assert(Self::allocators_bounded(kept, disk_au_count));
            assert(kept.len() <= count);
            assert(out.len() <= count);
        }
    }

    proof fn removable_partition_prefix_properties(
        allocators: Seq<PageAllocator>,
        count: nat,
        disk_au_count: IAU,
    )
        requires
            count <= allocators.len(),
            Self::allocators_wf(allocators),
            Self::allocators_unique(allocators),
            Self::allocators_bounded(allocators, disk_au_count),
            0 < page_count(),
        ensures
            Self::allocators_wf(
                Self::retained_allocated_prefix(allocators, count),
            ),
            Self::allocators_unique(
                Self::retained_allocated_prefix(allocators, count),
            ),
            Self::allocators_bounded(
                Self::retained_allocated_prefix(allocators, count),
                disk_au_count,
            ),
            Self::iau_seq_unique(
                Self::removable_aus_prefix(allocators, count),
            ),
            Self::retained_allocated_prefix(allocators, count).len()
                <= count,
            Self::removable_aus_prefix(allocators, count).len() <= count,
            iau_vec_set(Self::removable_aus_prefix(allocators, count))
                =~= (SpecMiniAllocator {
                    allocs: Self::allocators_i(
                        allocators.take(count as int),
                    ),
                    curr: None,
                }).removable_aus(),
            Self::allocators_i(
                Self::retained_allocated_prefix(allocators, count),
            ) == Self::allocators_i(
                allocators.take(count as int),
            ).remove_keys(iau_vec_set(
                Self::removable_aus_prefix(allocators, count),
            )),
        decreases count,
    {
        if count > 0 {
            let prior_count: nat = (count - 1) as nat;
            let source_before = allocators.take(prior_count as int);
            let source = allocators.take(count as int);
            let allocator = allocators[prior_count as int];
            let kept_before = Self::retained_allocated_prefix(
                allocators,
                prior_count,
            );
            let kept = Self::retained_allocated_prefix(
                allocators,
                count,
            );
            let out_before = Self::removable_aus_prefix(
                allocators,
                prior_count,
            );
            let out = Self::removable_aus_prefix(allocators, count);
            let removed_before = iau_vec_set(out_before);
            let removed = iau_vec_set(out);
            let source_before_i = Self::allocators_i(source_before);
            let source_i = Self::allocators_i(source);
            let kept_before_i = Self::allocators_i(kept_before);
            let kept_i = Self::allocators_i(kept);

            Self::removable_partition_prefix_properties(
                allocators,
                prior_count,
                disk_au_count,
            );
            assert(source == source_before.push(allocator));
            assert(Self::allocators_unique(source));
            Self::allocators_i_push(source_before, allocator);
            Self::page_allocator_empty_iff_zero(allocator);

            if allocator.next_page() == 0 {
                assert(kept == kept_before);
                assert(out == out_before.push(allocator.alloc_au()));
                Self::iau_vec_set_push(out_before, allocator.alloc_au());
                assert(removed =~= removed_before.insert(
                    allocator.alloc_au_nat(),
                ));
                assert(Self::iau_seq_unique(out)) by {
                    assert forall |i: int, j: int|
                        0 <= i < out.len()
                        && 0 <= j < out.len()
                        && #[trigger] out[i] == #[trigger] out[j]
                        implies i == j by {
                        if i < out_before.len() && j < out_before.len() {
                            assert(Self::iau_seq_unique(out_before));
                        } else if i == out_before.len()
                            && j < out_before.len()
                        {
                            assert(removed_before.contains(
                                allocator.alloc_au_nat(),
                            ));
                            assert(source_before_i.contains_key(
                                allocator.alloc_au_nat(),
                            ));
                            let old_idx = choose |k: int|
                                0 <= k < source_before.len()
                                && #[trigger] source_before[k]
                                    .alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx]
                                == source_before[old_idx]);
                            assert(source[source_before.len() as int]
                                == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        } else if j == out_before.len()
                            && i < out_before.len()
                        {
                            assert(removed_before.contains(
                                allocator.alloc_au_nat(),
                            ));
                            assert(source_before_i.contains_key(
                                allocator.alloc_au_nat(),
                            ));
                            let old_idx = choose |k: int|
                                0 <= k < source_before.len()
                                && #[trigger] source_before[k]
                                    .alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx]
                                == source_before[old_idx]);
                            assert(source[source_before.len() as int]
                                == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        }
                    }
                }
                assert(kept_i
                    == source_i.remove_keys(removed)) by {
                    assert_maps_equal!(
                        kept_i,
                        source_i.remove_keys(removed),
                        au => {}
                    );
                }
                assert(removed =~= (SpecMiniAllocator {
                    allocs: source_i,
                    curr: None,
                }).removable_aus()) by {
                    assert_sets_equal!(
                        removed,
                        (SpecMiniAllocator {
                            allocs: source_i,
                            curr: None,
                        }).removable_aus(),
                        au => {
                            if au == allocator.alloc_au_nat() {
                                assert(Self::page_allocator_i(allocator)
                                    .has_no_allocated_pages());
                            }
                        }
                    );
                }
            } else {
                assert(kept == kept_before.push(allocator));
                assert(out == out_before);
                assert(removed == removed_before);
                assert(Self::allocators_unique(kept)) by {
                    assert forall |i: int, j: int|
                        0 <= i < kept.len()
                        && 0 <= j < kept.len()
                        && #[trigger] kept[i].alloc_au_nat()
                            == #[trigger] kept[j].alloc_au_nat()
                        implies i == j by {
                        if i < kept_before.len() && j < kept_before.len() {
                            assert(Self::allocators_unique(kept_before));
                        } else if i == kept_before.len()
                            && j < kept_before.len()
                        {
                            assert(kept_before_i.contains_key(
                                allocator.alloc_au_nat(),
                            ));
                            assert(source_before_i.contains_key(
                                allocator.alloc_au_nat(),
                            ));
                            let old_idx = choose |k: int|
                                0 <= k < source_before.len()
                                && #[trigger] source_before[k]
                                    .alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx]
                                == source_before[old_idx]);
                            assert(source[source_before.len() as int]
                                == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        } else if j == kept_before.len()
                            && i < kept_before.len()
                        {
                            assert(kept_before_i.contains_key(
                                allocator.alloc_au_nat(),
                            ));
                            assert(source_before_i.contains_key(
                                allocator.alloc_au_nat(),
                            ));
                            let old_idx = choose |k: int|
                                0 <= k < source_before.len()
                                && #[trigger] source_before[k]
                                    .alloc_au_nat()
                                    == allocator.alloc_au_nat();
                            assert(source[old_idx]
                                == source_before[old_idx]);
                            assert(source[source_before.len() as int]
                                == allocator);
                            assert(false) by {
                                assert(Self::allocators_unique(source));
                            }
                        }
                    }
                }
                Self::allocators_i_push(kept_before, allocator);
                assert(kept_i
                    == source_i.remove_keys(removed)) by {
                    assert_maps_equal!(
                        kept_i,
                        source_i.remove_keys(removed),
                        au => {}
                    );
                }
                assert(removed =~= (SpecMiniAllocator {
                    allocs: source_i,
                    curr: None,
                }).removable_aus()) by {
                    assert_sets_equal!(
                        removed,
                        (SpecMiniAllocator {
                            allocs: source_i,
                            curr: None,
                        }).removable_aus(),
                        au => {
                            if au == allocator.alloc_au_nat() {
                                assert(!Self::page_allocator_i(allocator)
                                    .has_no_allocated_pages());
                            }
                        }
                    );
                }
            }

            assert(Self::allocators_wf(kept));
            assert(Self::allocators_bounded(kept, disk_au_count));
            assert(kept.len() <= count);
            assert(out.len() <= count);
        }
    }

    pub fn prune_removable_aus(
        &mut self,
        disk_au_count: IAU,
    ) -> (out: Vec<IAU>)
        requires
            old(self).wf(),
            Self::allocators_unique(old(self).allocators@),
            old(self).bounded(disk_au_count),
            0 < page_count(),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@),
            self.bounded(disk_au_count),
            self.threshold() == old(self).threshold(),
            out.len() <= old(self).allocators.len(),
            iau_vec_set(out@) =~= old(self).i().removable_aus(),
            Self::iau_seq_unique(out@),
            self.i() == old(self).i().prune(iau_vec_set(out@)),
            Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(old(self).allocators@)
                    - iau_vec_set(out@),
    {
        let ghost pre = *self;
        let saved_curr = self.curr;
        let saved_threshold = self.free_au_threshold;
        let mut kept = Vec::<PageAllocator>::new();
        let mut out = Vec::<IAU>::new();
        let mut idx: usize = 0;
        while idx < self.allocators.len()
            invariant
                idx <= self.allocators.len(),
                *self == pre,
                kept@ == Self::retained_allocated_prefix(
                    self.allocators@,
                    idx as nat,
                ),
                out@ == Self::removable_aus_prefix(
                    self.allocators@,
                    idx as nat,
                ),
            decreases self.allocators.len() - idx,
        {
            let allocator = PageAllocator::new(
                self.allocators[idx].au,
                self.allocators[idx].next_page,
            );
            proof {
                assert(allocator == self.allocators@[idx as int]);
            }
            if allocator.next_page == 0 {
                out.push(allocator.au);
            } else {
                kept.push(allocator);
            }
            proof {
                assert(Self::retained_allocated_prefix(
                    self.allocators@,
                    (idx + 1) as nat,
                ) == if allocator.next_page() > 0 {
                    Self::retained_allocated_prefix(
                        self.allocators@,
                        idx as nat,
                    ).push(allocator)
                } else {
                    Self::retained_allocated_prefix(
                        self.allocators@,
                        idx as nat,
                    )
                });
                assert(Self::removable_aus_prefix(
                    self.allocators@,
                    (idx + 1) as nat,
                ) == if allocator.next_page() == 0 {
                    Self::removable_aus_prefix(
                        self.allocators@,
                        idx as nat,
                    ).push(allocator.alloc_au())
                } else {
                    Self::removable_aus_prefix(
                        self.allocators@,
                        idx as nat,
                    )
                });
            }
            idx += 1;
        }

        proof {
            Self::removable_partition_prefix_properties(
                pre.allocators@,
                idx as nat,
                disk_au_count,
            );
            assert(pre.allocators@.take(idx as int) == pre.allocators@);
        }
        self.allocators = kept;
        let ghost removed = iau_vec_set(out@);
        let removed_curr = match saved_curr {
            Some(curr) => iau_vec_contains(&out, curr),
            None => false,
        };
        if removed_curr {
            self.curr = None;
        }
        self.free_au_threshold = saved_threshold;

        proof {
            assert(removed_curr == (pre.curr is Some
                && removed.contains(pre.curr.unwrap() as nat)));
            assert(self.curr == if pre.curr is Some
                    && removed.contains(pre.curr.unwrap() as nat)
                { None } else { pre.curr });
            assert(removed =~= pre.i().removable_aus());
            assert(Self::allocators_i(self.allocators@)
                == Self::allocators_i(pre.allocators@)
                    .remove_keys(removed));
            assert(self.i().allocs
                == pre.i().allocs.remove_keys(removed));
            pre.i().prune_preserves_wf(removed);
            assert(self.i() == pre.i().prune(removed));
            assert(Self::allocators_wf(self.allocators@));
            assert(Self::allocators_unique(self.allocators@));
            assert(Self::iau_seq_unique(out@));
            assert(self.bounded(disk_au_count));
            if self.curr is Some {
                assert(self.i().allocs.contains_key(
                    self.curr.unwrap() as nat,
                ));
            }
            assert(self.wf());
            Self::allocators_i_dom(pre.allocators@);
            Self::allocators_i_dom(self.allocators@);
            assert(Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(pre.allocators@) - removed) by {
                assert_sets_equal!(
                    Self::allocators_au_set(self.allocators@),
                    Self::allocators_au_set(pre.allocators@) - removed,
                    au => {}
                );
            }
        }
        out
    }

    pub fn prune_allocated_aus(
        &mut self,
        disk_au_count: IAU,
    ) -> (out: Vec<IAU>)
        requires
            old(self).wf(),
            Self::allocators_unique(old(self).allocators@),
            old(self).bounded(disk_au_count),
            0 < page_count(),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@),
            self.bounded(disk_au_count),
            self.threshold() == old(self).threshold(),
            out.len() <= old(self).allocators.len(),
            iau_vec_set(out@) =~= old(self).i().allocated_aus(),
            Self::iau_seq_unique(out@),
            self.i() == old(self).i().prune(iau_vec_set(out@)),
            Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(old(self).allocators@) - iau_vec_set(out@),
    {
        let ghost pre = *self;
        let saved_curr = self.curr;
        let saved_threshold = self.free_au_threshold;
        let mut kept = Vec::<PageAllocator>::new();
        let mut out = Vec::<IAU>::new();
        let mut idx: usize = 0;
        while idx < self.allocators.len()
            invariant
                idx <= self.allocators.len(),
                *self == pre,
                kept@ == Self::retained_prefix(self.allocators@, idx as nat),
                out@ == Self::allocated_aus_prefix(self.allocators@, idx as nat),
            decreases self.allocators.len() - idx,
        {
            let allocator = PageAllocator::new(
                self.allocators[idx].au,
                self.allocators[idx].next_page,
            );
            proof {
                assert(allocator.alloc_au() == self.allocators@[idx as int].alloc_au());
                assert(allocator.next_page() == self.allocators@[idx as int].next_page());
                assert(allocator == self.allocators@[idx as int]);
            }
            if allocator.next_page == 0 {
                kept.push(allocator);
            } else {
                out.push(allocator.au);
            }
            proof {
                assert(Self::retained_prefix(self.allocators@, (idx + 1) as nat)
                    == if allocator.next_page() == 0 {
                        Self::retained_prefix(self.allocators@, idx as nat).push(allocator)
                    } else {
                        Self::retained_prefix(self.allocators@, idx as nat)
                    });
                assert(Self::allocated_aus_prefix(self.allocators@, (idx + 1) as nat)
                    == if allocator.next_page() > 0 {
                        Self::allocated_aus_prefix(self.allocators@, idx as nat)
                            .push(allocator.alloc_au())
                    } else {
                        Self::allocated_aus_prefix(self.allocators@, idx as nat)
                    });
            }
            idx = idx + 1;
        }

        proof {
            assert(idx == pre.allocators@.len());
            Self::partition_prefix_properties(
                pre.allocators@,
                idx as nat,
                disk_au_count,
            );
            assert(pre.allocators@.take(idx as int) == pre.allocators@);
            assert(kept@ == Self::retained_prefix(pre.allocators@, idx as nat));
            assert(out@ == Self::allocated_aus_prefix(pre.allocators@, idx as nat));
        }

        self.allocators = kept;
        let ghost removed = iau_vec_set(out@);
        let removed_curr = match saved_curr {
            Some(curr) => iau_vec_contains(&out, curr),
            None => false,
        };
        if removed_curr {
            self.curr = None;
        }
        self.free_au_threshold = saved_threshold;

        proof {
            assert(idx == pre.allocators@.len());
            assert(removed_curr == (pre.curr is Some
                && removed.contains(pre.curr.unwrap() as nat)));
            assert(self.curr == if pre.curr is Some
                    && removed.contains(pre.curr.unwrap() as nat)
                { None } else { pre.curr });
            let ghost source_model = SpecMiniAllocator{
                allocs: Self::allocators_i(pre.allocators@),
                curr: None,
            };
            assert(removed =~= source_model.allocated_aus());
            assert(source_model.allocs == pre.i().allocs);
            assert(source_model.allocated_aus() =~= pre.i().allocated_aus()) by {
                assert_sets_equal!(
                    source_model.allocated_aus(),
                    pre.i().allocated_aus(),
                    au => {}
                );
            }
            assert(removed =~= pre.i().allocated_aus());
            assert(Self::allocators_i(self.allocators@)
                == Self::allocators_i(pre.allocators@).remove_keys(removed));
            assert(self.i().allocs == pre.i().allocs.remove_keys(removed));
            pre.i().prune_preserves_wf(removed);
            assert(self.i() == pre.i().prune(removed));
            assert(Self::allocators_wf(self.allocators@));
            assert(Self::allocators_unique(self.allocators@));
            assert(Self::iau_seq_unique(out@));
            assert(self.bounded(disk_au_count));
            if self.curr is Some {
                assert(self.i().allocs.contains_key(self.curr.unwrap() as nat));
                assert(exists |i: int| 0 <= i < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat()
                        == self.curr.unwrap() as nat);
            }
            assert(self.wf());
            Self::allocators_i_dom(pre.allocators@);
            Self::allocators_i_dom(self.allocators@);
            assert(Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(pre.allocators@) - removed) by {
                assert_sets_equal!(
                    Self::allocators_au_set(self.allocators@),
                    Self::allocators_au_set(pre.allocators@) - removed,
                    au => {}
                );
            }
        }
        out
    }

    pub fn prune_aus(
        &mut self,
        aus: &Vec<IAU>,
        disk_au_count: IAU,
    )
        requires
            old(self).wf(),
            Self::allocators_unique(old(self).allocators@),
            old(self).bounded(disk_au_count),
            0 < page_count(),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@),
            self.bounded(disk_au_count),
            self.threshold() == old(self).threshold(),
            self.i() == old(self).i().prune(iau_vec_set(aus@)),
            Self::allocators_au_set(self.allocators@)
                =~= Self::allocators_au_set(old(self).allocators@)
                    - iau_vec_set(aus@),
    {
        let ghost pre = *self;
        let ghost removed = iau_vec_set(aus@);
        let saved_curr = self.curr;
        let saved_threshold = self.free_au_threshold;
        let mut kept = Vec::<PageAllocator>::new();
        let mut idx: usize = 0;
        while idx < self.allocators.len()
            invariant
                *self == pre,
                idx <= self.allocators.len(),
                Self::allocators_wf(kept@),
                Self::allocators_unique(kept@),
                Self::allocators_bounded(kept@, disk_au_count),
                kept@.len() <= idx,
                Self::allocators_i(kept@)
                    == Self::allocators_i(
                        self.allocators@.take(idx as int),
                    ).remove_keys(removed),
            decreases self.allocators.len() - idx,
        {
            let allocator = PageAllocator::new(
                self.allocators[idx].au,
                self.allocators[idx].next_page,
            );
            let remove = iau_vec_contains(aus, allocator.au);
            let ghost prior_kept = kept@;
            let ghost source_before = self.allocators@.take(idx as int);
            let ghost source = self.allocators@.take((idx + 1) as int);
            proof {
                assert(allocator == self.allocators@[idx as int]);
                assert(source == source_before.push(allocator));
                Self::allocators_i_push(source_before, allocator);
                assert(remove == removed.contains(
                    allocator.alloc_au_nat(),
                ));
            }
            if !remove {
                kept.push(allocator);
                proof {
                    assert(Self::allocators_wf(kept@));
                    assert(Self::allocators_bounded(
                        kept@,
                        disk_au_count,
                    ));
                    assert(Self::allocators_unique(kept@)) by {
                        assert forall |i: int, j: int| {
                            &&& 0 <= i < kept@.len()
                            &&& 0 <= j < kept@.len()
                            &&& #[trigger] kept@[i].alloc_au_nat()
                                == #[trigger] kept@[j].alloc_au_nat()
                        } implies i == j by {
                            if i < prior_kept.len()
                                && j < prior_kept.len()
                            {
                                assert(Self::allocators_unique(prior_kept));
                            } else if i == prior_kept.len()
                                && j < prior_kept.len()
                            {
                                assert(Self::allocators_i(prior_kept)
                                    .contains_key(
                                        allocator.alloc_au_nat(),
                                    ));
                                assert(Self::allocators_i(source_before)
                                    .contains_key(
                                        allocator.alloc_au_nat(),
                                    ));
                                let old_idx = choose |k: int|
                                    0 <= k < idx as int
                                    && #[trigger] self.allocators@[k]
                                        .alloc_au_nat()
                                        == allocator.alloc_au_nat();
                                assert(false) by {
                                    assert(Self::allocators_unique(
                                        self.allocators@,
                                    ));
                                }
                            } else if j == prior_kept.len()
                                && i < prior_kept.len()
                            {
                                assert(Self::allocators_i(prior_kept)
                                    .contains_key(
                                        allocator.alloc_au_nat(),
                                    ));
                                assert(Self::allocators_i(source_before)
                                    .contains_key(
                                        allocator.alloc_au_nat(),
                                    ));
                                let old_idx = choose |k: int|
                                    0 <= k < idx as int
                                    && #[trigger] self.allocators@[k]
                                        .alloc_au_nat()
                                        == allocator.alloc_au_nat();
                                assert(false) by {
                                    assert(Self::allocators_unique(
                                        self.allocators@,
                                    ));
                                }
                            }
                        }
                    }
                    Self::allocators_i_push(prior_kept, allocator);
                    assert(Self::allocators_i(kept@)
                        == Self::allocators_i(source)
                            .remove_keys(removed)) by {
                        assert_maps_equal!(
                            Self::allocators_i(kept@),
                            Self::allocators_i(source)
                                .remove_keys(removed),
                            au => {}
                        );
                    }
                }
            } else {
                proof {
                    assert(Self::allocators_i(kept@)
                        == Self::allocators_i(source)
                            .remove_keys(removed)) by {
                        assert_maps_equal!(
                            Self::allocators_i(kept@),
                            Self::allocators_i(source)
                                .remove_keys(removed),
                            au => {}
                        );
                    }
                }
            }
            idx += 1;
        }

        proof {
            assert(self.allocators@.take(idx as int)
                == self.allocators@);
        }
        self.allocators = kept;
        let removed_curr = match saved_curr {
            Some(curr) => iau_vec_contains(aus, curr),
            None => false,
        };
        if removed_curr {
            self.curr = None;
        }
        self.free_au_threshold = saved_threshold;

        proof {
            assert(removed_curr == (pre.curr is Some
                && removed.contains(pre.curr.unwrap() as nat)));
            assert(self.curr == if pre.curr is Some
                    && removed.contains(pre.curr.unwrap() as nat)
                { None } else { pre.curr });
            assert(Self::allocators_i(self.allocators@)
                == Self::allocators_i(pre.allocators@)
                    .remove_keys(removed));
            assert(self.i().allocs
                == pre.i().allocs.remove_keys(removed));
            pre.i().prune_preserves_wf(removed);
            assert(self.i() == pre.i().prune(removed));
            assert(self.wf());
            Self::allocators_i_dom(pre.allocators@);
            Self::allocators_i_dom(self.allocators@);
        }
    }

    pub fn peek_next_addr(&self) -> (out: IAddress)
        requires
            self.allocation_ready(),
        ensures
            out.au == self.alloc_au(),
            out.page == self.next_page(),
            out@.au == self.alloc_au_nat(),
            out@ == self.next_addr(),
            self.next_addr_wf() ==> out@.wf(),
    {
        let active_idx = self.allocators.len() - 1;
        proof {
            assert(0 < self.allocators@.len());
            assert(active_idx as int == self.allocators@.len() - 1);
        }
        let out = self.allocators[active_idx].peek_next_addr();
        proof {
            assert(self.allocators@[active_idx as int] == self.active_allocator());
            assert(out@ == self.next_addr());
            if self.next_addr_wf() {
                reveal(MiniAllocatorImpl::next_addr_wf);
                assert(out@.wf());
            }
        }
        out
    }

    pub fn advance_next_addr(&mut self)
        requires
            old(self).allocation_ready(),
        ensures
            self.wf(),
            Self::allocators_unique(old(self).allocators@)
                ==> Self::allocators_unique(self.allocators@),
            self.allocation_ready(),
            self.alloc_au() == old(self).alloc_au(),
            self.alloc_au_nat() == old(self).alloc_au_nat(),
            self.next_page() == old(self).next_page() + 1,
            self.threshold() == old(self).threshold(),
            ({
                let addr = Address{
                    au: old(self).alloc_au_nat(),
                    page: old(self).next_page() as nat,
                };
                Self::allocators_unique(old(self).allocators@)
                && old(self).next_addr_wf()
                && old(self).i().can_allocate(addr)
                && old(self).i().allocate(addr).curr == old(self).i().curr
            }) ==> self.i() == old(self).i().allocate(Address{
                au: old(self).alloc_au_nat(),
                page: old(self).next_page() as nat,
            }),
    {
        let ghost pre_allocators = self.allocators@;
        let mut active = self.allocators.pop().unwrap();
        proof {
            assert(active == pre_allocators[pre_allocators.len() - 1]);
        }
        active.advance_next_addr();
        let ghost post_active = active;
        self.allocators.push(active);
        proof {
            assert(self.allocators@ == pre_allocators.drop_last().push(post_active));
            assert(post_active.wf());
            assert forall |i: int| 0 <= i < self.allocators@.len()
                implies #[trigger] self.allocators@[i].wf() by {
                if i == self.allocators@.len() - 1 {
                    assert(self.allocators@[i] == post_active);
                } else {
                    assert(self.allocators@[i] == pre_allocators[i]);
                    assert(pre_allocators[i].wf());
                }
            }
            if Self::allocators_unique(old(self).allocators@) {
                assert(Self::allocators_unique(self.allocators@)) by {
                    assert forall |i: int, j: int| 0 <= i < self.allocators@.len()
                        && 0 <= j < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat()
                            == #[trigger] self.allocators@[j].alloc_au_nat()
                        implies i == j by {
                        if i == self.allocators@.len() - 1 {
                            if j == self.allocators@.len() - 1 {
                            } else {
                                assert(self.allocators@[i] == post_active);
                                assert(self.allocators@[j] == pre_allocators[j]);
                                assert(post_active.alloc_au_nat()
                                    == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
                                assert(pre_allocators[pre_allocators.len() - 1].alloc_au_nat()
                                    == pre_allocators[j].alloc_au_nat());
                                assert(Self::allocators_unique(pre_allocators));
                                assert(false);
                            }
                        } else if j == self.allocators@.len() - 1 {
                            assert(self.allocators@[i] == pre_allocators[i]);
                            assert(self.allocators@[j] == post_active);
                            assert(post_active.alloc_au_nat()
                                == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
                            assert(pre_allocators[i].alloc_au_nat()
                                == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
                            assert(Self::allocators_unique(pre_allocators));
                            assert(false);
                        } else {
                            assert(self.allocators@[i] == pre_allocators[i]);
                            assert(self.allocators@[j] == pre_allocators[j]);
                            assert(Self::allocators_unique(pre_allocators));
                        }
                    }
                }
            }
            if self.curr is Some {
                let curr_au = self.curr.unwrap();
                assert(old(self).wf());
                assert(exists |i: int| 0 <= i < pre_allocators.len()
                    && #[trigger] pre_allocators[i].alloc_au_nat() == curr_au as nat);
                let curr_idx = choose |i: int| 0 <= i < pre_allocators.len()
                    && #[trigger] pre_allocators[i].alloc_au_nat() == curr_au as nat;
                if curr_idx == pre_allocators.len() - 1 {
                    assert(self.allocators@[self.allocators@.len() - 1] == post_active);
                    assert(post_active.alloc_au_nat() == pre_allocators[curr_idx].alloc_au_nat());
                } else {
                    assert(self.allocators@[curr_idx] == pre_allocators[curr_idx]);
                }
                assert(exists |i: int| 0 <= i < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat() == curr_au as nat);
            }
            self.prove_curr_in_i_allocs();
            assert(self.wf());
            assert(self.active_allocator() == post_active);
            assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
            assert(post_active.alloc_au() == pre_allocators[pre_allocators.len() - 1].alloc_au());
            assert(post_active.alloc_au_nat() == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
            assert(old(self).active_allocator().alloc_au()
                == pre_allocators[pre_allocators.len() - 1].alloc_au());
            assert(old(self).alloc_au_nat() == old(self).alloc_au() as nat);
            post_active.alloc_au_nat_is_alloc_au();
            assert(post_active.alloc_au_nat() == post_active.alloc_au() as nat);
            assert(post_active.next_page() == pre_allocators[pre_allocators.len() - 1].next_page() + 1);
            let addr = Address{
                au: old(self).alloc_au_nat(),
                page: old(self).next_page() as nat,
            };
            if Self::allocators_unique(old(self).allocators@)
                && old(self).next_addr_wf()
                && old(self).i().can_allocate(addr)
                && old(self).i().allocate(addr).curr == old(self).i().curr {
                reveal(MiniAllocatorImpl::next_addr_wf);
                assert(addr.wf());
                assert(old(self).i().allocs.contains_key(addr.au));
                assert(old(self).i().allocs[addr.au].is_free_addr(addr));
                assert(old(self).alloc_au_nat() == addr.au);
                assert(self.i().curr == old(self).i().allocate(addr).curr);
                assert(self.i().allocs =~= old(self).i().allocate(addr).allocs) by {
                    assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                        == old(self).i().allocate(addr).allocs.contains_key(au) by {
                        if self.i().allocs.contains_key(au) {
                            let idx = choose |i: int| 0 <= i < self.allocators@.len()
                                && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                            if idx == self.allocators@.len() - 1 {
                                assert(self.allocators@[idx] == post_active);
                                assert(post_active.alloc_au_nat() == old(self).alloc_au_nat());
                                assert(old(self).alloc_au_nat() == addr.au);
                                assert(au == addr.au);
                                assert(old(self).i().allocs.contains_key(au));
                            } else {
                                assert(self.allocators@[idx] == pre_allocators[idx]);
                                assert(old(self).i().allocs.contains_key(au));
                            }
                        }
                        if old(self).i().allocate(addr).allocs.contains_key(au) {
                            assert(old(self).i().allocs.contains_key(au));
                            let old_idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                                && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                            if old_idx == old(self).allocators@.len() - 1 {
                                assert(self.allocators@[self.allocators@.len() - 1].alloc_au_nat() == au);
                            } else {
                                assert(self.allocators@[old_idx] == old(self).allocators@[old_idx]);
                            }
                            assert(self.i().allocs.contains_key(au));
                        }
                    }
                    assert forall |au: AU| self.i().allocs.contains_key(au) implies
                        #[trigger] self.i().allocs[au]
                            == old(self).i().allocate(addr).allocs[au] by {
                        let idx = choose |i: int| 0 <= i < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                        let old_idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                            && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                        if au == addr.au {
                            assert(old(self).allocators@[old(self).allocators@.len() - 1].alloc_au_nat()
                                == addr.au);
                            assert(Self::allocators_unique(old(self).allocators@));
                            assert(old_idx == old(self).allocators@.len() - 1);
                            assert(self.allocators@[self.allocators@.len() - 1].alloc_au_nat()
                                == addr.au);
                            assert(self.allocators@[idx].alloc_au_nat() == au);
                            assert(idx == self.allocators@.len() - 1);
                            assert(self.allocators@[idx] == post_active);
                            assert(old(self).allocators@[old_idx] == old(self).active_allocator());
                            assert(Self::page_allocator_i(post_active).allocated
                                =~= old(self).i().allocs[au].allocated + set![addr]) by {
                                assert forall |a: Address| #[trigger] Self::page_allocator_i(post_active).allocated.contains(a)
                                    == (old(self).i().allocs[au].allocated + set![addr]).contains(a) by {
                                    if Self::page_allocator_i(post_active).allocated.contains(a) {
                                        assert(a.au == au);
                                        assert(a.page < post_active.next_page() as nat);
                                        if a.page == addr.page {
                                            assert(a == addr);
                                        } else {
                                            assert(a.page < old(self).next_page() as nat) by {
                                                assert(a.page < old(self).next_page() as nat + 1);
                                                assert(a.page != old(self).next_page() as nat);
                                            }
                                            assert(old(self).i().allocs[au].allocated.contains(a));
                                        }
                                    }
                                    if (old(self).i().allocs[au].allocated + set![addr]).contains(a) {
                                        if a == addr {
                                            assert(a.page < post_active.next_page() as nat);
                                        } else {
                                            assert(old(self).i().allocs[au].allocated.contains(a));
                                            assert(a.page < old(self).next_page() as nat);
                                            assert(a.page < post_active.next_page() as nat);
                                        }
                                    }
                                }
                            }
                            assert(old(self).i().allocate(addr).allocs[au].allocated
                                == old(self).i().allocs[au].allocated + set![addr]);
                            assert(Self::page_allocator_i(post_active).allocated
                                == old(self).i().allocate(addr).allocs[au].allocated);
                            assert(Self::page_allocator_i(post_active).au
                                == old(self).i().allocs[au].au);
                        } else {
                            if idx == self.allocators@.len() - 1 {
                                assert(self.allocators@[idx] == post_active);
                                assert(post_active.alloc_au_nat() == old(self).alloc_au_nat());
                                assert(old(self).alloc_au_nat() == addr.au);
                                assert(au == addr.au);
                                assert(false);
                            }
                            assert(idx != self.allocators@.len() - 1);
                            assert(self.allocators@[idx] == old(self).allocators@[idx]);
                            assert(old_idx == idx);
                        }
                    }
                }
                assert(self.i() == old(self).i().allocate(addr));
            }
        }
    }

    pub fn allocate_fresh_addr(&mut self) -> (out: Option<IAddress>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            out is Some ==> old(self).allocation_ready(),
            out is Some ==> self.allocation_ready(),
            out is Some ==> out.unwrap().au == old(self).alloc_au(),
            out is Some ==> out.unwrap().page == old(self).next_page(),
            out is None ==> *self == *old(self),
    {
        if self.allocators.len() == 0 {
            proof {
                assert(self.i() == old(self).i());
            }
            None
        } else {
            let ghost pre_allocators = self.allocators@;
            let mut active = self.allocators.pop().unwrap();
            proof {
                assert(active == pre_allocators[pre_allocators.len() - 1]);
            }
            let out = active.peek_next_addr();
            active.advance_next_addr();
            let ghost post_active = active;
            self.allocators.push(active);
            self.curr = Some(out.au);
            proof {
                assert(self.allocators@ == pre_allocators.drop_last().push(post_active));
                assert(post_active.wf());
                assert forall |i: int| 0 <= i < self.allocators@.len()
                    implies #[trigger] self.allocators@[i].wf() by {
                    if i == self.allocators@.len() - 1 {
                        assert(self.allocators@[i] == post_active);
                    } else {
                        assert(self.allocators@[i] == pre_allocators[i]);
                        assert(pre_allocators[i].wf());
                    }
                }
                let curr_idx = self.allocators@.len() - 1;
                assert(self.curr is Some);
                assert(self.curr.unwrap() == out.au);
                assert(self.allocators@[curr_idx] == post_active);
                assert(out.au == pre_allocators[pre_allocators.len() - 1].alloc_au());
                assert(post_active.alloc_au() == pre_allocators[pre_allocators.len() - 1].alloc_au());
                assert(exists |i: int| 0 <= i < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat() == self.curr.unwrap() as nat);
                self.prove_curr_in_i_allocs();
                assert(self.wf());
                assert(self.allocation_ready());
                assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
                assert(out.au == old(self).alloc_au());
                assert(out.page == old(self).next_page());
            }
            Some(out)
        }
    }

    pub fn allocate_fresh_addr_checked(
        &mut self,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: Option<IAddress>)
        requires
            old(self).wf(),
            Self::allocators_unique(old(self).allocators@),
            Self::allocators_bounded(old(self).allocators@, disk_au_count),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == page_count(),
        ensures
            self.wf(),
            out is Some ==> old(self).allocation_ready(),
            out is Some ==> self.allocation_ready(),
            out is Some ==> out.unwrap().au == old(self).alloc_au(),
            out is Some ==> out.unwrap().page == old(self).next_page(),
            out is Some ==> out.unwrap()@.wf(),
            out is Some ==> old(self).i().can_allocate(out.unwrap()@),
            out is Some ==> self.i() == old(self).i().allocate(out.unwrap()@),
            Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(old(self).allocators@),
            Self::allocators_unique(self.allocators@),
            old(self).bounded(disk_au_count) ==> self.bounded(disk_au_count),
            old(self).allocation_ready() && (old(self).next_page() as nat) < (disk_page_count as nat)
                ==> out is Some,
            out is None ==> *self == *old(self),
    {
        if self.allocators.len() == 0 {
            proof {
                assert(self.i() == old(self).i());
            }
            return None;
        }

        let root = self.peek_next_addr();
        if root.page >= disk_page_count {
            proof {
                assert(self.i() == old(self).i());
            }
            return None;
        }

        proof {
            old(self).prove_active_next_addr_can_allocate(disk_au_count, disk_page_count);
            assert(old(self).i().can_allocate(root@));
        }

        let ghost pre_allocators = self.allocators@;
        let mut active = self.allocators.pop().unwrap();
        proof {
            assert(active == pre_allocators[pre_allocators.len() - 1]);
        }
        let out = active.peek_next_addr();
        active.advance_next_addr();
        let ghost post_active = active;
        self.allocators.push(active);
        if out.page == disk_page_count - 1 {
            self.curr = None;
        } else {
            self.curr = Some(out.au);
        }
        proof {
            let addr = Address{
                au: old(self).alloc_au_nat(),
                page: old(self).next_page() as nat,
            };
            assert(root == out);
            assert(out@ == addr);
            assert(addr.wf());
            assert(self.allocators@ == pre_allocators.drop_last().push(post_active));
            assert(post_active.wf());
            assert forall |i: int| 0 <= i < self.allocators@.len()
                implies #[trigger] self.allocators@[i].wf() by {
                if i == self.allocators@.len() - 1 {
                    assert(self.allocators@[i] == post_active);
                } else {
                    assert(self.allocators@[i] == pre_allocators[i]);
                    assert(pre_allocators[i].wf());
                }
            }
            if self.curr is Some {
                let curr_au = self.curr.unwrap();
                assert(curr_au == out.au);
                assert(self.allocators@[self.allocators@.len() - 1] == post_active);
                assert(post_active.alloc_au_nat() == out.au as nat);
                assert(exists |i: int| 0 <= i < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat() == curr_au as nat);
            }
            self.prove_curr_in_i_allocs();
            assert(self.wf());
            assert(self.allocation_ready());
            assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
            assert(out.au == old(self).alloc_au());
            assert(out.page == old(self).next_page());
            assert(post_active.alloc_au() == pre_allocators[pre_allocators.len() - 1].alloc_au());
            assert(post_active.alloc_au_nat() == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
            post_active.alloc_au_nat_is_alloc_au();
            assert(post_active.alloc_au_nat() == post_active.alloc_au() as nat);
            assert(post_active.next_page() == pre_allocators[pre_allocators.len() - 1].next_page() + 1);
            assert(old(self).i().can_allocate(addr));
            assert(old(self).i().allocs.contains_key(addr.au));
            assert(old(self).i().allocs[addr.au].is_free_addr(addr));
            assert(old(self).alloc_au_nat() == addr.au);
            assert(Self::page_allocator_i(post_active).allocated
                =~= old(self).i().allocs[addr.au].allocated + set![addr]) by {
                assert forall |a: Address| #[trigger] Self::page_allocator_i(post_active).allocated.contains(a)
                    == (old(self).i().allocs[addr.au].allocated + set![addr]).contains(a) by {
                    if Self::page_allocator_i(post_active).allocated.contains(a) {
                        assert(a.au == addr.au);
                        assert(a.page < post_active.next_page() as nat);
                        if a.page == addr.page {
                            assert(a == addr);
                        } else {
                            assert(a.page < old(self).next_page() as nat) by {
                                assert(a.page < old(self).next_page() as nat + 1);
                                assert(a.page != old(self).next_page() as nat);
                            }
                            assert(old(self).i().allocs[addr.au].allocated.contains(a));
                        }
                    }
                    if (old(self).i().allocs[addr.au].allocated + set![addr]).contains(a) {
                        if a == addr {
                            assert(a.page < post_active.next_page() as nat);
                        } else {
                            assert(old(self).i().allocs[addr.au].allocated.contains(a));
                            assert(a.page < old(self).next_page() as nat);
                            assert(a.page < post_active.next_page() as nat);
                        }
                    }
                }
            }
            assert(old(self).i().allocate(addr).allocs[addr.au].allocated
                == old(self).i().allocs[addr.au].allocated + set![addr]);
            assert(Self::page_allocator_i(post_active).allocated
                == old(self).i().allocate(addr).allocs[addr.au].allocated);
            assert(Self::page_allocator_i(post_active).au
                == old(self).i().allocs[addr.au].au);

            Self::page_allocator_prefix_all_pages_allocated(post_active, disk_page_count);
            if out.page == disk_page_count - 1 {
                assert(post_active.next_page() as nat == disk_page_count as nat);
                assert(Self::page_allocator_i(post_active).all_pages_allocated());
                assert(old(self).i().allocate(addr).curr is None);
                assert(self.i().curr is None);
            } else {
                assert(out.page < disk_page_count - 1);
                assert((post_active.next_page() as nat) < (disk_page_count as nat));
                assert(!Self::page_allocator_i(post_active).all_pages_allocated());
                assert(old(self).i().allocate(addr).curr == Some(addr.au));
                assert(self.i().curr == Some(addr.au));
            }

            assert(self.i().allocs =~= old(self).i().allocate(addr).allocs) by {
                assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                    == old(self).i().allocate(addr).allocs.contains_key(au) by {
                    if self.i().allocs.contains_key(au) {
                        let idx = choose |i: int| 0 <= i < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                        if idx == self.allocators@.len() - 1 {
                            assert(self.allocators@[idx] == post_active);
                            assert(post_active.alloc_au_nat() == old(self).alloc_au_nat());
                            assert(old(self).alloc_au_nat() == addr.au);
                            assert(au == addr.au);
                            assert(old(self).i().allocs.contains_key(au));
                        } else {
                            assert(self.allocators@[idx] == pre_allocators[idx]);
                            assert(old(self).i().allocs.contains_key(au));
                        }
                    }
                    if old(self).i().allocate(addr).allocs.contains_key(au) {
                        assert(old(self).i().allocs.contains_key(au));
                        let old_idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                            && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                        if old_idx == old(self).allocators@.len() - 1 {
                            assert(self.allocators@[self.allocators@.len() - 1].alloc_au_nat() == au);
                        } else {
                            assert(self.allocators@[old_idx] == old(self).allocators@[old_idx]);
                        }
                        assert(self.i().allocs.contains_key(au));
                    }
                }
                assert forall |au: AU| self.i().allocs.contains_key(au) implies
                    #[trigger] self.i().allocs[au]
                        == old(self).i().allocate(addr).allocs[au] by {
                    let idx = choose |i: int| 0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                    let old_idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                        && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                    if au == addr.au {
                        assert(old(self).allocators@[old(self).allocators@.len() - 1].alloc_au_nat()
                            == addr.au);
                        assert(Self::allocators_unique(old(self).allocators@));
                        assert(old_idx == old(self).allocators@.len() - 1);
                        assert(self.allocators@[self.allocators@.len() - 1].alloc_au_nat()
                            == addr.au);
                        assert(self.allocators@[idx].alloc_au_nat() == au);
                        assert(idx == self.allocators@.len() - 1);
                        assert(self.allocators@[idx] == post_active);
                    } else {
                        if idx == self.allocators@.len() - 1 {
                            assert(self.allocators@[idx] == post_active);
                            assert(post_active.alloc_au_nat() == old(self).alloc_au_nat());
                            assert(old(self).alloc_au_nat() == addr.au);
                            assert(au == addr.au);
                            assert(false);
                        }
                        assert(idx != self.allocators@.len() - 1);
                        assert(self.allocators@[idx] == old(self).allocators@[idx]);
                        assert(old_idx == idx);
                    }
                }
            }
            assert(self.i() == old(self).i().allocate(addr));
            assert(Self::allocators_au_set(self.allocators@)
                =~= Self::allocators_au_set(old(self).allocators@)) by {
                assert forall |au: AU| #[trigger] Self::allocators_au_set(self.allocators@).contains(au)
                    implies Self::allocators_au_set(old(self).allocators@).contains(au) by {
                    let idx = choose |i: int| 0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                    if idx == self.allocators@.len() - 1 {
                        assert(self.allocators@[idx] == post_active);
                        assert(post_active.alloc_au_nat()
                            == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
                        assert(old(self).allocators@[old(self).allocators@.len() - 1].alloc_au_nat()
                            == au);
                    } else {
                        assert(self.allocators@[idx] == pre_allocators[idx]);
                        assert(old(self).allocators@[idx].alloc_au_nat() == au);
                    }
                }
                assert forall |au: AU| #[trigger] Self::allocators_au_set(old(self).allocators@).contains(au)
                    implies Self::allocators_au_set(self.allocators@).contains(au) by {
                    let idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                        && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                    if idx == old(self).allocators@.len() - 1 {
                        assert(self.allocators@[self.allocators@.len() - 1] == post_active);
                        assert(post_active.alloc_au_nat()
                            == old(self).allocators@[idx].alloc_au_nat());
                    } else {
                        assert(self.allocators@[idx] == old(self).allocators@[idx]);
                    }
                }
            }
            assert forall |i: int| 0 <= i < self.allocators@.len()
                implies #[trigger] self.allocators@[i].alloc_au_nat()
                    == #[trigger] pre_allocators[i].alloc_au_nat() by {
                if i == self.allocators@.len() - 1 {
                    assert(self.allocators@[i] == post_active);
                    assert(post_active.alloc_au_nat()
                        == pre_allocators[pre_allocators.len() - 1].alloc_au_nat());
                    assert(i == pre_allocators.len() - 1);
                } else {
                    assert(self.allocators@[i] == pre_allocators[i]);
                }
            }
            assert(Self::allocators_unique(self.allocators@)) by {
                assert forall |i: int, j: int| 0 <= i < self.allocators@.len()
                    && 0 <= j < self.allocators@.len()
                    && #[trigger] self.allocators@[i].alloc_au_nat()
                        == #[trigger] self.allocators@[j].alloc_au_nat()
                    implies i == j by {
                    assert(self.allocators@[i].alloc_au_nat() == pre_allocators[i].alloc_au_nat());
                    assert(self.allocators@[j].alloc_au_nat() == pre_allocators[j].alloc_au_nat());
                    assert(pre_allocators[i].alloc_au_nat() == pre_allocators[j].alloc_au_nat());
                    assert(Self::allocators_unique(pre_allocators));
                }
            }
        }
        Some(out)
    }

    pub fn add_aus(&mut self, aus: Vec<IAU>)
        requires
            old(self).wf(),
            Self::allocators_unique(old(self).allocators@),
            Self::iau_seq_unique(aus@),
            iau_vec_set(aus@).disjoint(Self::allocators_au_set(old(self).allocators@)),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@),
            Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(old(self).allocators@) + iau_vec_set(aus@),
            self.threshold() == old(self).threshold(),
            self.curr == old(self).curr,
            self.i() == old(self).i().add_aus(iau_vec_set(aus@)),
            old(self).i().allocated_aus() == Set::<AU>::empty()
                ==> self.i().allocated_aus() == Set::<AU>::empty(),
            forall |total_aus: IAU| old(self).bounded(total_aus)
                && (forall |i: int| 0 <= i < aus@.len()
                    ==> 0 < (#[trigger] aus@[i] as nat) && (aus@[i] as nat) < (total_aus as nat))
                ==> self.bounded(total_aus),
    {
        let saved_threshold = self.free_au_threshold;
        let saved_curr = self.curr;
        let mut idx: usize = 0;
        while idx < aus.len()
            invariant
                idx <= aus.len(),
                Self::allocators_wf(self.allocators@),
                Self::allocators_unique(self.allocators@),
                self.allocators@.len() == old(self).allocators@.len() + idx,
                forall |i: int| 0 <= i < old(self).allocators@.len()
                    ==> #[trigger] self.allocators@[i] == old(self).allocators@[i],
	                forall |j: int| 0 <= j < idx ==> {
	                    &&& #[trigger] self.allocators@[old(self).allocators@.len() + j].alloc_au_nat()
	                        == aus@[j] as nat
	                    &&& self.allocators@[old(self).allocators@.len() + j].next_page() == 0
	                },
	                self.free_au_threshold == saved_threshold,
                self.curr == saved_curr,
                saved_curr is Some ==> exists |i: int|
                    0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == saved_curr.unwrap() as nat,
            decreases aus.len() - idx
        {
            let ghost pre_allocators = self.allocators@;
            proof {
                assert forall |j: int| 0 <= j < idx implies {
                    &&& #[trigger] pre_allocators[old(self).allocators@.len() + j].alloc_au_nat()
                        == aus@[j] as nat
                    &&& pre_allocators[old(self).allocators@.len() + j].next_page() == 0
                } by {
                    assert(pre_allocators == self.allocators@);
                }
            }
            self.allocators.push(PageAllocator::new(aus[idx], 0));
            proof {
                assert(self.allocators@ == pre_allocators.push(self.allocators@[self.allocators@.len() - 1]));
                assert(self.allocators@[self.allocators@.len() - 1].wf());
                assert forall |i: int| 0 <= i < self.allocators@.len()
                    implies #[trigger] self.allocators@[i].wf() by {
                    if i == pre_allocators.len() {
                        assert(self.allocators@[i].wf());
                    } else {
                        assert(self.allocators@[i] == pre_allocators[i]);
                        assert(pre_allocators[i].wf());
                    }
                }
                assert(self.allocators@[(pre_allocators.len() as int)].alloc_au_nat() == aus@[idx as int] as nat);
                assert(self.allocators@[(pre_allocators.len() as int)].next_page() == 0);
                assert(Self::allocators_unique(self.allocators@)) by {
                    assert forall |i: int, j: int| 0 <= i < self.allocators@.len()
                        && 0 <= j < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat()
                            == #[trigger] self.allocators@[j].alloc_au_nat()
                        implies i == j by {
                        let old_len = old(self).allocators@.len();
                        if i < old_len && j < old_len {
                            assert(self.allocators@[i] == old(self).allocators@[i]);
                            assert(self.allocators@[j] == old(self).allocators@[j]);
                            assert(Self::allocators_unique(old(self).allocators@));
                            assert(i == j);
                        } else if i < old_len {
                            assert(self.allocators@[i] == old(self).allocators@[i]);
                            if j == self.allocators@.len() - 1 {
                                assert(self.allocators@[j].alloc_au_nat() == aus@[idx as int] as nat);
                                assert(iau_vec_set(aus@).contains(self.allocators@[j].alloc_au_nat()));
                            } else {
                                assert(old_len <= j < pre_allocators.len());
                                let prev = j - old_len;
                                assert(0 <= prev < idx);
                                assert(self.allocators@[j].alloc_au_nat() == aus@[prev] as nat);
                                assert(iau_vec_set(aus@).contains(self.allocators@[j].alloc_au_nat()));
                            }
                            assert(Self::allocators_au_set(old(self).allocators@).contains(
                                self.allocators@[i].alloc_au_nat()));
                            assert(false);
                        } else if j < old_len {
                            assert(self.allocators@[j] == old(self).allocators@[j]);
                            if i == self.allocators@.len() - 1 {
                                assert(self.allocators@[i].alloc_au_nat() == aus@[idx as int] as nat);
                                assert(iau_vec_set(aus@).contains(self.allocators@[i].alloc_au_nat()));
                            } else {
                                assert(old_len <= i < pre_allocators.len());
                                let prev = i - old_len;
                                assert(0 <= prev < idx);
                                assert(self.allocators@[i].alloc_au_nat() == aus@[prev] as nat);
                                assert(iau_vec_set(aus@).contains(self.allocators@[i].alloc_au_nat()));
                            }
                            assert(Self::allocators_au_set(old(self).allocators@).contains(
                                self.allocators@[j].alloc_au_nat()));
                            assert(false);
                        } else {
                            let ii = i - old_len;
                            let jj = j - old_len;
                            assert(0 <= ii < idx + 1);
                            assert(0 <= jj < idx + 1);
                            if i == self.allocators@.len() - 1 {
                                assert(ii == idx);
                                assert(self.allocators@[i].alloc_au_nat() == aus@[ii] as nat);
                            } else {
                                assert(ii < idx);
                                assert(i == old_len + ii);
                                assert(i < pre_allocators.len());
                                assert(self.allocators@[i] == pre_allocators[i]);
                                assert(pre_allocators[i].alloc_au_nat() == aus@[ii] as nat);
                                assert(self.allocators@[i].alloc_au_nat() == aus@[ii] as nat);
                            }
                            if j == self.allocators@.len() - 1 {
                                assert(jj == idx);
                                assert(self.allocators@[j].alloc_au_nat() == aus@[jj] as nat);
                            } else {
                                assert(jj < idx);
                                assert(j == old_len + jj);
                                assert(j < pre_allocators.len());
                                assert(self.allocators@[j] == pre_allocators[j]);
                                assert(pre_allocators[j].alloc_au_nat() == aus@[jj] as nat);
                                assert(self.allocators@[j].alloc_au_nat() == aus@[jj] as nat);
                            }
                            assert(aus@[ii] == aus@[jj]);
                            assert(Self::iau_seq_unique(aus@));
                            assert(ii == jj);
                            assert(i == j);
                        }
                    }
                }
                assert forall |i: int| 0 <= i < old(self).allocators@.len()
                    implies #[trigger] self.allocators@[i] == old(self).allocators@[i] by {
                    assert(self.allocators@[i] == pre_allocators[i]);
                }
                assert forall |j: int| 0 <= j < idx + 1 implies {
                    &&& #[trigger] self.allocators@[old(self).allocators@.len() + j].alloc_au_nat()
                        == aus@[j] as nat
                    &&& self.allocators@[old(self).allocators@.len() + j].next_page() == 0
                } by {
                    if j == idx {
                        assert(self.allocators@[old(self).allocators@.len() + j]
                            == self.allocators@[(pre_allocators.len() as int)]);
                    } else {
                        assert(self.allocators@[old(self).allocators@.len() + j]
                            == pre_allocators[old(self).allocators@.len() + j]);
                    }
                }
                if saved_curr is Some {
                    assert(exists |i: int| 0 <= i < pre_allocators.len()
                        && #[trigger] pre_allocators[i].alloc_au_nat() == saved_curr.unwrap() as nat);
                    let curr_idx = choose |i: int| 0 <= i < pre_allocators.len()
                        && #[trigger] pre_allocators[i].alloc_au_nat() == saved_curr.unwrap() as nat;
                    assert(self.allocators@[curr_idx] == pre_allocators[curr_idx]);
                    assert(exists |i: int| 0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == saved_curr.unwrap() as nat);
                }
            }
            idx = idx + 1;
        }
        proof {
            self.prove_curr_in_i_allocs();
            assert(self.wf());
            assert(Self::allocators_au_set(self.allocators@) =~=
                Self::allocators_au_set(old(self).allocators@) + iau_vec_set(aus@)) by {
                assert forall |au: AU| #[trigger] Self::allocators_au_set(self.allocators@).contains(au)
                    implies (Self::allocators_au_set(old(self).allocators@) + iau_vec_set(aus@)).contains(au) by {
                    let found_idx = choose |i: int| 0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                    if found_idx < old(self).allocators@.len() {
                        assert(self.allocators@[found_idx] == old(self).allocators@[found_idx]);
                        assert(Self::allocators_au_set(old(self).allocators@).contains(au));
                    } else {
                        let new_idx = found_idx - old(self).allocators@.len();
                        assert(idx == aus.len());
                        assert(0 <= new_idx < aus@.len());
                        assert(0 <= new_idx < idx);
                        assert(found_idx == old(self).allocators@.len() + new_idx);
                        assert(self.allocators@[old(self).allocators@.len() + new_idx].alloc_au_nat()
                            == aus@[new_idx] as nat);
                        assert(self.allocators@[found_idx].alloc_au_nat() == aus@[new_idx] as nat);
                        assert(iau_vec_set(aus@).contains(au));
                    }
                }
                assert forall |au: AU|
                    #[trigger] (Self::allocators_au_set(old(self).allocators@) + iau_vec_set(aus@)).contains(au)
                    implies Self::allocators_au_set(self.allocators@).contains(au) by {
                    if Self::allocators_au_set(old(self).allocators@).contains(au) {
                        let idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                            && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                        assert(self.allocators@[idx] == old(self).allocators@[idx]);
                        assert(Self::allocators_au_set(self.allocators@).contains(au));
                    } else {
                        assert(iau_vec_set(aus@).contains(au));
                        let idx = choose |i: int| 0 <= i < aus@.len()
                            && #[trigger] aus@[i] as nat == au;
                        let post_idx = old(self).allocators@.len() + idx;
                        assert(0 <= post_idx < self.allocators@.len());
                        assert(self.allocators@[post_idx].alloc_au_nat() == aus@[idx] as nat);
                        assert(Self::allocators_au_set(self.allocators@).contains(au));
                    }
                }
            }
            assert(self.free_au_threshold == saved_threshold);
            assert(self.curr == saved_curr);
            let added = iau_vec_set(aus@);
            let spec_post = old(self).i().add_aus(added);
            assert(self.i().curr == spec_post.curr);
            assert(self.i().allocs =~= spec_post.allocs) by {
                assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                    implies spec_post.allocs.contains_key(au) by {
                    let post_idx = choose |i: int| 0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                    if post_idx < old(self).allocators@.len() {
                        assert(old(self).allocators@[post_idx].alloc_au_nat() == au);
                        assert(old(self).i().allocs.contains_key(au));
                    } else {
                        let new_idx = post_idx - old(self).allocators@.len();
                        assert(0 <= new_idx < aus@.len());
                        assert(post_idx == old(self).allocators@.len() + new_idx);
                        assert(self.allocators@[post_idx].alloc_au_nat() == aus@[new_idx] as nat);
                        assert(added.contains(au));
                    }
                }
                assert forall |au: AU| #[trigger] spec_post.allocs.contains_key(au)
                    implies self.i().allocs.contains_key(au) by {
                    if old(self).i().allocs.contains_key(au) {
                        let old_idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                            && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                        assert(self.allocators@[old_idx] == old(self).allocators@[old_idx]);
                        assert(self.i().allocs.contains_key(au));
                    } else {
                        assert(added.contains(au));
                        let new_idx = choose |i: int| 0 <= i < aus@.len()
                            && #[trigger] (aus@[i] as nat) == au;
                        let post_idx = old(self).allocators@.len() + new_idx;
                        assert(0 <= post_idx < self.allocators@.len());
                        assert(self.allocators@[post_idx].alloc_au_nat() == au);
                        assert(self.i().allocs.contains_key(au));
                    }
                }
                assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                    implies self.i().allocs[au] == spec_post.allocs[au] by {
                    let post_idx = choose |i: int| 0 <= i < self.allocators@.len()
                        && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                    if old(self).i().allocs.contains_key(au) {
                        assert(!added.contains(au));
                        if !(post_idx < old(self).allocators@.len()) {
                            let new_idx = post_idx - old(self).allocators@.len();
                            assert(0 <= new_idx < aus@.len());
                            assert(post_idx == old(self).allocators@.len() + new_idx);
                            assert(self.allocators@[post_idx].alloc_au_nat() == aus@[new_idx] as nat);
                            assert(added.contains(au));
                            assert(false);
                        }
                        let old_idx = choose |i: int| 0 <= i < old(self).allocators@.len()
                            && #[trigger] old(self).allocators@[i].alloc_au_nat() == au;
                        assert(self.allocators@[post_idx] == old(self).allocators@[post_idx]);
                        assert(Self::allocators_unique(old(self).allocators@));
                        assert(old_idx == post_idx);
                        assert(self.i().allocs[au] == old(self).i().allocs[au]);
                        assert(spec_post.allocs[au] == old(self).i().allocs[au]);
                    } else {
                        assert(added.contains(au));
                        let new_idx = choose |i: int| 0 <= i < aus@.len()
                            && #[trigger] (aus@[i] as nat) == au;
                        let expected_idx = old(self).allocators@.len() + new_idx;
                        assert(0 <= expected_idx < self.allocators@.len());
                        assert(self.allocators@[expected_idx].alloc_au_nat() == au);
                        assert(self.allocators@[expected_idx].next_page() == 0);
                        assert(Self::allocators_unique(self.allocators@));
                        assert(post_idx == expected_idx);
                        let allocator = self.allocators@[post_idx];
                        assert(allocator.alloc_au_nat() == au);
                        assert(allocator.next_page() == 0);
                        assert(Self::page_allocator_allocated(allocator) =~= Set::<Address>::empty()) by {
                            assert forall |addr: Address| #[trigger] Self::page_allocator_allocated(allocator).contains(addr)
                                implies false by {
                                assert(addr.page < allocator.next_page() as nat);
                            }
                        }
                        assert(Self::page_allocator_i(allocator) == SpecMiniPageAllocator::new(au));
                        assert(self.i().allocs[au] == Self::page_allocator_i(allocator));
                        assert(spec_post.allocs[au] == SpecMiniPageAllocator::new(au));
                    }
                }
            }
            assert(self.i() == spec_post);
            if old(self).i().allocated_aus() == Set::<AU>::empty() {
                assert(self.i().allocated_aus() =~= Set::<AU>::empty()) by {
                    assert forall |au: AU| #[trigger] self.i().allocated_aus().contains(au)
                        implies false by {
                        assert(spec_post.allocated_aus().contains(au));
                        assert(spec_post.allocs.contains_key(au));
                        assert(!spec_post.allocs[au].has_no_allocated_pages());
                        if old(self).i().allocs.contains_key(au) {
                            assert(!old(self).i().allocs[au].has_no_allocated_pages());
                            assert(old(self).i().allocated_aus().contains(au));
                            assert(false);
                        } else {
                            assert(added.contains(au));
                            assert(spec_post.allocs[au] == SpecMiniPageAllocator::new(au));
                            assert(spec_post.allocs[au].allocated == Set::<Address>::empty());
                            assert(spec_post.allocs[au].has_no_allocated_pages());
                            assert(false);
                        }
                    }
                }
            }
            assert forall |total_aus: IAU| old(self).bounded(total_aus)
                && (forall |i: int| 0 <= i < aus@.len()
                    ==> 0 < (#[trigger] aus@[i] as nat) && (aus@[i] as nat) < (total_aus as nat))
                implies self.bounded(total_aus) by {
                assert forall |i: int| 0 <= i < self.allocators@.len()
                    implies {
                        &&& 0 < #[trigger] self.allocators@[i].alloc_au_nat()
                        &&& self.allocators@[i].alloc_au_nat() < (total_aus as nat)
                    } by {
                    if i < old(self).allocators@.len() {
                        assert(self.allocators@[i] == old(self).allocators@[i]);
                        assert(old(self).bounded(total_aus));
                    } else {
                        let new_idx = i - old(self).allocators@.len();
                        assert(0 <= new_idx < aus@.len());
                        assert(idx == aus.len());
                        assert(i == old(self).allocators@.len() + new_idx);
                        assert(0 <= new_idx < idx);
                        assert(self.allocators@[i].alloc_au_nat() == aus@[new_idx] as nat);
                    }
                }
            }
        }
    }

    pub fn refill_from_pool(
        &mut self,
        pool: &mut AuPoolImpl,
        total_aus: IAU,
    ) -> (out: Option<AuAllocation>)
        requires
            old(self).allocation_ready(),
            Self::allocators_unique(old(self).allocators@),
            old(pool).canonical_wf(total_aus),
            old(pool)@.disjoint(Self::allocators_au_set(old(self).allocators@)),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@),
            self.allocation_ready(),
            self.alloc_au() == old(self).alloc_au(),
            self.alloc_au_nat() == old(self).alloc_au_nat(),
            self.next_page() == old(self).next_page(),
            pool.canonical_wf(total_aus),
            pool@.disjoint(Self::allocators_au_set(self.allocators@)),
            self.threshold() == old(self).threshold(),
            old(self).bounded(total_aus) ==> self.bounded(total_aus),
            match out {
                Some(allocation) => {
                    &&& allocation.wf(total_aus)
                    &&& allocation.as_set() <= old(pool)@
                    &&& pool@ =~= old(pool)@ - allocation.as_set()
                    &&& self.i() == old(self).i().add_aus(allocation.as_set())
                },
                None => {
                    &&& *self == *old(self)
                    &&& *pool == *old(pool)
                },
            },
    {
        let saved_threshold = self.free_au_threshold;
        let saved_curr = self.curr;
        let free_count = self.free_au_count();
        if free_count >= self.free_au_threshold {
            proof {
                assert(self.free_au_threshold == saved_threshold);
                assert(pool@ =~= old(pool)@);
                assert(self.i() == old(self).i());
                assert(self.allocators@ == old(self).allocators@);
                assert(self.curr == old(self).curr);
                assert(self.free_au_threshold == old(self).free_au_threshold);
                assert(self.allocation_ready());
                assert(self.alloc_au() == old(self).alloc_au());
                assert(self.alloc_au_nat() == old(self).alloc_au_nat());
                assert(self.next_page() == old(self).next_page());
            }
            return None;
        }

        let needed = self.free_au_threshold - free_count;
        match pool.alloc(total_aus, needed) {
            None => {
                proof {
                    assert(self.free_au_threshold == saved_threshold);
                    assert(self.allocation_ready());
                    assert(self.alloc_au() == old(self).alloc_au());
                    assert(self.alloc_au_nat() == old(self).alloc_au_nat());
                    assert(self.next_page() == old(self).next_page());
                }
                None
            },
            Some(allocation) => {
                proof {
                    au_allocation_vec_unique(allocation, total_aus);
                    au_allocation_vec_set_matches(allocation, total_aus);
                    assert(iau_vec_set(allocation.aus@).disjoint(
                        Self::allocators_au_set(self.allocators@),
                    )) by {
                        assert(iau_vec_set(allocation.aus@) =~= allocation.as_set());
                        assert(allocation.as_set() <= old(pool)@);
                        assert(old(pool)@.disjoint(Self::allocators_au_set(self.allocators@)));
                    }
                }
                let ghost pre_allocators = self.allocators@;
                let active = self.allocators.pop().unwrap();
                proof {
                    assert(saved_curr == old(self).curr);
                    assert(pre_allocators == old(self).allocators@);
                    assert(active == pre_allocators[pre_allocators.len() - 1]);
                    assert(self.allocators@ == pre_allocators.drop_last());
                    assert forall |i: int| 0 <= i < self.allocators@.len()
                        implies #[trigger] self.allocators@[i].wf() by {
                        assert(self.allocators@[i] == pre_allocators[i]);
                        assert(pre_allocators[i].wf());
                    }
                    assert(Self::allocators_unique(self.allocators@)) by {
                        assert forall |i: int, j: int| 0 <= i < self.allocators@.len()
                            && 0 <= j < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat()
                                == #[trigger] self.allocators@[j].alloc_au_nat()
                            implies i == j by {
                            assert(self.allocators@[i] == pre_allocators[i]);
                            assert(self.allocators@[j] == pre_allocators[j]);
                            assert(Self::allocators_unique(pre_allocators));
                        }
                    }
                }

                let mut idx: usize = 0;
                while idx < allocation.aus.len()
                    invariant
                        idx <= allocation.aus.len(),
                        Self::allocators_wf(self.allocators@),
                        Self::allocators_unique(self.allocators@),
                        self.curr == saved_curr,
                        self.allocators@.len() == pre_allocators.drop_last().len() + idx,
                        forall |i: int| 0 <= i < pre_allocators.drop_last().len()
                            ==> #[trigger] self.allocators@[i] == pre_allocators[i],
                        forall |j: int| 0 <= j < idx ==> {
                            &&& #[trigger] self.allocators@[pre_allocators.drop_last().len() + j].alloc_au_nat()
                                == allocation.aus@[j] as nat
                            &&& self.allocators@[pre_allocators.drop_last().len() + j].next_page() == 0
                        },
                    decreases allocation.aus.len() - idx
                {
                    let ghost pre_push_allocators = self.allocators@;
                    self.allocators.push(PageAllocator::new(allocation.aus[idx], 0));
                    proof {
                        assert(self.allocators@ == pre_push_allocators.push(self.allocators@[self.allocators@.len() - 1]));
                        assert(self.allocators@[self.allocators@.len() - 1].wf());
                        assert forall |i: int| 0 <= i < self.allocators@.len()
                            implies #[trigger] self.allocators@[i].wf() by {
                            if i == pre_push_allocators.len() {
                                assert(self.allocators@[i].wf());
                            } else {
                                assert(self.allocators@[i] == pre_push_allocators[i]);
                                assert(pre_push_allocators[i].wf());
                            }
                        }
                        assert forall |i: int| 0 <= i < pre_allocators.drop_last().len()
                            implies #[trigger] self.allocators@[i] == pre_allocators[i] by {
                            assert(pre_push_allocators[i] == pre_allocators[i]);
                            assert(self.allocators@[i] == pre_push_allocators[i]);
                        }
                        assert(self.allocators@[pre_push_allocators.len() as int].alloc_au_nat()
                            == allocation.aus@[idx as int] as nat);
                        assert(self.allocators@[pre_push_allocators.len() as int].next_page() == 0);
                        assert(Self::allocators_unique(self.allocators@)) by {
                            assert forall |i: int, j: int| 0 <= i < self.allocators@.len()
                                && 0 <= j < self.allocators@.len()
                                && #[trigger] self.allocators@[i].alloc_au_nat()
                                    == #[trigger] self.allocators@[j].alloc_au_nat()
                                implies i == j by {
                                let prefix_len = pre_allocators.drop_last().len();
                                if i == self.allocators@.len() - 1 {
                                    if j == self.allocators@.len() - 1 {
                                    } else if j < prefix_len {
                                        assert(self.allocators@[j] == pre_allocators[j]);
                                        assert(Self::allocators_au_set(pre_allocators).contains(
                                            self.allocators@[j].alloc_au_nat()));
                                        assert(iau_vec_set(allocation.aus@).contains(
                                            self.allocators@[i].alloc_au_nat()));
                                        assert(iau_vec_set(allocation.aus@).disjoint(
                                            Self::allocators_au_set(pre_allocators),
                                        ));
                                        assert(false);
                                    } else {
                                        let prev = j - prefix_len;
                                        assert(0 <= prev < idx);
                                        assert(pre_push_allocators[j] == self.allocators@[j]);
                                        assert(pre_push_allocators[prefix_len + prev].alloc_au_nat()
                                            == allocation.aus@[prev] as nat);
                                        assert(self.allocators@[j].alloc_au_nat()
                                            == allocation.aus@[prev] as nat);
                                        assert(self.allocators@[i].alloc_au_nat()
                                            == allocation.aus@[idx as int] as nat);
                                        assert(MiniAllocatorImpl::iau_seq_unique(allocation.aus@));
                                        assert(prev == idx);
                                        assert(false);
                                    }
                                } else if j == self.allocators@.len() - 1 {
                                    if i < prefix_len {
                                        assert(self.allocators@[i] == pre_allocators[i]);
                                        assert(Self::allocators_au_set(pre_allocators).contains(
                                            self.allocators@[i].alloc_au_nat()));
                                        assert(iau_vec_set(allocation.aus@).contains(
                                            self.allocators@[j].alloc_au_nat()));
                                        assert(iau_vec_set(allocation.aus@).disjoint(
                                            Self::allocators_au_set(pre_allocators),
                                        ));
                                        assert(false);
                                    } else {
                                        let prev = i - prefix_len;
                                        assert(0 <= prev < idx);
                                        assert(pre_push_allocators[i] == self.allocators@[i]);
                                        assert(pre_push_allocators[prefix_len + prev].alloc_au_nat()
                                            == allocation.aus@[prev] as nat);
                                        assert(self.allocators@[i].alloc_au_nat()
                                            == allocation.aus@[prev] as nat);
                                        assert(self.allocators@[j].alloc_au_nat()
                                            == allocation.aus@[idx as int] as nat);
                                        assert(MiniAllocatorImpl::iau_seq_unique(allocation.aus@));
                                        assert(prev == idx);
                                        assert(false);
                                    }
                                } else {
                                    assert(pre_push_allocators[i] == self.allocators@[i]);
                                    assert(pre_push_allocators[j] == self.allocators@[j]);
                                    assert(Self::allocators_unique(pre_push_allocators));
                                }
                            }
                        }
                        assert forall |j: int| 0 <= j < idx + 1
                            implies #[trigger] self.allocators@[
                                pre_allocators.drop_last().len() + j
                            ].next_page() == 0 by {
                            let post_idx = pre_allocators.drop_last().len() + j;
                            if j == idx {
                                assert(pre_push_allocators.len()
                                    == pre_allocators.drop_last().len() + idx);
                                assert(post_idx == pre_push_allocators.len());
                                assert(self.allocators@[post_idx].next_page() == 0);
                            } else {
                                assert(0 <= j < idx);
                                assert(pre_push_allocators[
                                    pre_allocators.drop_last().len() + j
                                ].alloc_au_nat() == allocation.aus@[j] as nat);
                                assert(pre_push_allocators[
                                    pre_allocators.drop_last().len() + j
                                ].next_page() == 0);
                                assert(self.allocators@[post_idx]
                                    == pre_push_allocators[post_idx]);
                            }
                        }
                    }
                    idx = idx + 1;
                }

                let ghost before_active_push = self.allocators@;
                proof {
                    assert(idx == allocation.aus.len());
                    assert forall |j: int| 0 <= j < allocation.aus@.len()
                        implies #[trigger] before_active_push[
                            pre_allocators.drop_last().len() + j
                        ].next_page() == 0 by {
                        assert(before_active_push == self.allocators@);
                        assert(0 <= j < idx);
                        assert(self.allocators@[
                            pre_allocators.drop_last().len() + j
                        ].alloc_au_nat() == allocation.aus@[j] as nat);
                        assert(self.allocators@[
                            pre_allocators.drop_last().len() + j
                        ].next_page() == 0);
                    }
                }
                self.allocators.push(active);
                self.free_au_threshold = saved_threshold;
                proof {
                    assert(active.wf());
                    assert(self.allocators@ == before_active_push.push(active));
                    assert forall |i: int| 0 <= i < self.allocators@.len()
                        implies #[trigger] self.allocators@[i].wf() by {
                        if i == before_active_push.len() {
                            assert(self.allocators@[i] == active);
                        } else {
                            assert(self.allocators@[i] == before_active_push[i]);
                            assert(before_active_push[i].wf());
                        }
                    }
                    assert(Self::allocators_unique(self.allocators@)) by {
                        assert forall |i: int, j: int| 0 <= i < self.allocators@.len()
                            && 0 <= j < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat()
                                == #[trigger] self.allocators@[j].alloc_au_nat()
                            implies i == j by {
                            if i == before_active_push.len() {
                                if j == before_active_push.len() {
                                } else {
                                    assert(self.allocators@[i] == active);
                                    if j < pre_allocators.drop_last().len() {
                                        assert(self.allocators@[j] == pre_allocators[j]);
                                        assert(active == pre_allocators[pre_allocators.len() - 1]);
                                        assert(Self::allocators_unique(pre_allocators));
                                        assert(false);
                                    } else {
                                        let new_idx = j - pre_allocators.drop_last().len();
                                        assert(0 <= new_idx < allocation.aus@.len());
                                        assert(self.allocators@[j] == before_active_push[j]);
                                        assert(before_active_push[pre_allocators.drop_last().len() + new_idx].alloc_au_nat()
                                            == allocation.aus@[new_idx] as nat);
                                        assert(self.allocators@[j].alloc_au_nat()
                                            == allocation.aus@[new_idx] as nat);
                                        assert(iau_vec_set(allocation.aus@).contains(
                                            self.allocators@[j].alloc_au_nat()));
                                        assert(Self::allocators_au_set(pre_allocators).contains(
                                            active.alloc_au_nat()));
                                        assert(iau_vec_set(allocation.aus@).disjoint(
                                            Self::allocators_au_set(pre_allocators),
                                        ));
                                        assert(false);
                                    }
                                }
                            } else if j == before_active_push.len() {
                                if i < pre_allocators.drop_last().len() {
                                    assert(self.allocators@[i] == pre_allocators[i]);
                                    assert(self.allocators@[j] == active);
                                    assert(active == pre_allocators[pre_allocators.len() - 1]);
                                    assert(Self::allocators_unique(pre_allocators));
                                    assert(false);
                                } else {
                                    let new_idx = i - pre_allocators.drop_last().len();
                                    assert(0 <= new_idx < allocation.aus@.len());
                                    assert(self.allocators@[i] == before_active_push[i]);
                                    assert(before_active_push[pre_allocators.drop_last().len() + new_idx].alloc_au_nat()
                                        == allocation.aus@[new_idx] as nat);
                                    assert(self.allocators@[i].alloc_au_nat()
                                        == allocation.aus@[new_idx] as nat);
                                    assert(iau_vec_set(allocation.aus@).contains(
                                        self.allocators@[i].alloc_au_nat()));
                                    assert(self.allocators@[j] == active);
                                    assert(Self::allocators_au_set(pre_allocators).contains(
                                        active.alloc_au_nat()));
                                    assert(iau_vec_set(allocation.aus@).disjoint(
                                        Self::allocators_au_set(pre_allocators),
                                    ));
                                    assert(false);
                                }
                            } else {
                                assert(before_active_push[i] == self.allocators@[i]);
                                assert(before_active_push[j] == self.allocators@[j]);
                                assert(Self::allocators_unique(before_active_push));
                            }
                        }
                    }
                    if self.curr is Some {
                        let curr_au = self.curr.unwrap();
                        assert(old(self).wf());
                        assert(self.curr == saved_curr);
                        assert(saved_curr == old(self).curr);
                        assert(exists |i: int| 0 <= i < pre_allocators.len()
                            && #[trigger] pre_allocators[i].alloc_au_nat() == curr_au as nat);
                        let curr_idx = choose |i: int| 0 <= i < pre_allocators.len()
                            && #[trigger] pre_allocators[i].alloc_au_nat() == curr_au as nat;
                        if curr_idx == pre_allocators.len() - 1 {
                            assert(self.allocators@[self.allocators@.len() - 1] == active);
                            assert(active.alloc_au_nat() == pre_allocators[curr_idx].alloc_au_nat());
                        } else {
                            assert(curr_idx < before_active_push.len());
                            assert(curr_idx < pre_allocators.drop_last().len());
                            assert(before_active_push[curr_idx] == pre_allocators[curr_idx]);
                            assert(self.allocators@[curr_idx] == before_active_push[curr_idx]);
                        }
                        assert(exists |i: int| 0 <= i < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat() == curr_au as nat);
                    }
                    self.prove_curr_in_i_allocs();
                    assert(self.wf());
                    assert(self.allocation_ready());
                    assert(self.active_allocator() == active);
                    assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
                    assert(active == old(self).active_allocator());
                    assert(self.alloc_au() == old(self).alloc_au());
                    assert(self.alloc_au_nat() == old(self).alloc_au_nat());
                    assert(self.next_page() == old(self).next_page());
                    assert(self.free_au_threshold == saved_threshold);
                    let added = iau_vec_set(allocation.aus@);
                    let spec_post = old(self).i().add_aus(added);
                    assert(added =~= allocation.as_set());
                    let prefix_len = pre_allocators.drop_last().len();
                    let active_post_idx = before_active_push.len() as int;
                    assert(active_post_idx == self.allocators@.len() - 1);
                    assert(self.i().curr == spec_post.curr);
                    assert forall |j: int| 0 <= j < allocation.aus@.len()
                        implies #[trigger] before_active_push[prefix_len + j].alloc_au_nat()
                            == allocation.aus@[j] as nat by {
                        assert(before_active_push == self.allocators@.drop_last());
                    }
                    assert forall |j: int| 0 <= j < allocation.aus@.len()
                        implies #[trigger] before_active_push[prefix_len + j].next_page() == 0 by {
                        assert(before_active_push == self.allocators@.drop_last());
                    }
                    assert(self.i().allocs =~= spec_post.allocs) by {
                        assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                            implies spec_post.allocs.contains_key(au) by {
                            let post_idx = choose |i: int| 0 <= i < self.allocators@.len()
                                && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                            if post_idx == active_post_idx {
                                assert(self.allocators@[post_idx] == active);
                                assert(active == pre_allocators[pre_allocators.len() - 1]);
                                assert(old(self).i().allocs.contains_key(au));
                            } else if post_idx < prefix_len {
                                assert(self.allocators@[post_idx] == pre_allocators[post_idx]);
                                assert(old(self).i().allocs.contains_key(au));
                            } else {
                                let new_idx = post_idx - prefix_len;
                                assert(0 <= new_idx < allocation.aus@.len());
                                assert(self.allocators@[post_idx] == before_active_push[post_idx]);
                                assert(before_active_push[prefix_len + new_idx].alloc_au_nat()
                                    == allocation.aus@[new_idx] as nat);
                                assert(added.contains(au));
                            }
                        }
                        assert forall |au: AU| #[trigger] spec_post.allocs.contains_key(au)
                            implies self.i().allocs.contains_key(au) by {
                            if old(self).i().allocs.contains_key(au) {
                                let old_idx = choose |i: int| 0 <= i < pre_allocators.len()
                                    && #[trigger] pre_allocators[i].alloc_au_nat() == au;
                                if old_idx == pre_allocators.len() - 1 {
                                    assert(self.allocators@[active_post_idx] == active);
                                    assert(active == pre_allocators[old_idx]);
                                } else {
                                    assert(old_idx < prefix_len);
                                    assert(self.allocators@[old_idx] == pre_allocators[old_idx]);
                                }
                            } else {
                                assert(added.contains(au));
                                let new_idx = choose |i: int| 0 <= i < allocation.aus@.len()
                                    && #[trigger] allocation.aus@[i] as nat == au;
                                let post_idx = prefix_len + new_idx;
                                assert(0 <= post_idx < before_active_push.len());
                                assert(self.allocators@[post_idx] == before_active_push[post_idx]);
                                assert(before_active_push[post_idx].alloc_au_nat() == au);
                            }
                        }
                        assert forall |au: AU| #[trigger] self.i().allocs.contains_key(au)
                            implies self.i().allocs[au] == spec_post.allocs[au] by {
                            if old(self).i().allocs.contains_key(au) {
                                assert(!added.contains(au)) by {
                                    assert(Self::allocators_au_set(pre_allocators).contains(au));
                                    assert(added.disjoint(Self::allocators_au_set(pre_allocators)));
                                }
                                let old_idx = choose |i: int| 0 <= i < pre_allocators.len()
                                    && #[trigger] pre_allocators[i].alloc_au_nat() == au;
                                let post_idx = choose |i: int| 0 <= i < self.allocators@.len()
                                    && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                                if old_idx == pre_allocators.len() - 1 {
                                    assert(self.allocators@[active_post_idx] == active);
                                    assert(active == pre_allocators[old_idx]);
                                    assert(post_idx == active_post_idx) by {
                                        assert(Self::allocators_unique(self.allocators@));
                                    }
                                    assert(self.i().allocs[au] == Self::page_allocator_i(active));
                                    assert(old(self).i().allocs[au]
                                        == Self::page_allocator_i(pre_allocators[old_idx]));
                                    assert(spec_post.allocs[au] == old(self).i().allocs[au]);
                                } else {
                                    assert(old_idx < prefix_len);
                                    assert(self.allocators@[old_idx] == pre_allocators[old_idx]);
                                    assert(post_idx == old_idx) by {
                                        assert(Self::allocators_unique(self.allocators@));
                                    }
                                    assert(self.i().allocs[au]
                                        == Self::page_allocator_i(pre_allocators[old_idx]));
                                    assert(old(self).i().allocs[au]
                                        == Self::page_allocator_i(pre_allocators[old_idx]));
                                    assert(spec_post.allocs[au] == old(self).i().allocs[au]);
                                }
                            } else {
                                assert(added.contains(au));
                                let new_idx = choose |i: int| 0 <= i < allocation.aus@.len()
                                    && #[trigger] allocation.aus@[i] as nat == au;
                                let expected_idx = prefix_len + new_idx;
                                let post_idx = choose |i: int| 0 <= i < self.allocators@.len()
                                    && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                                assert(0 <= expected_idx < before_active_push.len());
                                assert(self.allocators@[expected_idx] == before_active_push[expected_idx]);
                                assert(before_active_push[expected_idx].alloc_au_nat() == au);
                                assert(before_active_push[expected_idx].next_page() == 0);
                                assert(post_idx == expected_idx) by {
                                    assert(Self::allocators_unique(self.allocators@));
                                }
                                let allocator = self.allocators@[post_idx];
                                assert(allocator.alloc_au_nat() == au);
                                assert(allocator.next_page() == 0);
                                assert(Self::page_allocator_allocated(allocator) =~= Set::<Address>::empty()) by {
                                    assert forall |addr: Address|
                                        #[trigger] Self::page_allocator_allocated(allocator).contains(addr)
                                        implies false by {
                                        assert(addr.page < allocator.next_page() as nat);
                                    }
                                }
                                assert(Self::page_allocator_i(allocator) == SpecMiniPageAllocator::new(au));
                                assert(spec_post.allocs[au] == SpecMiniPageAllocator::new(au));
                            }
                        }
                    }
                    assert(self.i() == spec_post);
                    assert(pool@.disjoint(Self::allocators_au_set(self.allocators@))) by {
                        assert(pool@ =~= old(pool)@ - allocation.as_set());
                        assert forall |au: AU| #[trigger] pool@.contains(au)
                            implies !Self::allocators_au_set(self.allocators@).contains(au) by {
                            assert(!allocation.as_set().contains(au));
                            if Self::allocators_au_set(self.allocators@).contains(au) {
                                let post_idx = choose |i: int| 0 <= i < self.allocators@.len()
                                    && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                                if post_idx == active_post_idx {
                                    assert(self.allocators@[post_idx] == active);
                                    assert(active == pre_allocators[pre_allocators.len() - 1]);
                                    assert(Self::allocators_au_set(pre_allocators).contains(au));
                                    assert(old(pool)@.disjoint(Self::allocators_au_set(pre_allocators)));
                                    assert(false);
                                } else if post_idx < prefix_len {
                                    assert(self.allocators@[post_idx] == pre_allocators[post_idx]);
                                    assert(Self::allocators_au_set(pre_allocators).contains(au));
                                    assert(old(pool)@.disjoint(Self::allocators_au_set(pre_allocators)));
                                    assert(false);
                                } else {
                                    let new_idx = post_idx - prefix_len;
                                    assert(0 <= new_idx < allocation.aus@.len());
                                    assert(self.allocators@[post_idx] == before_active_push[post_idx]);
                                    assert(before_active_push[prefix_len + new_idx].alloc_au_nat()
                                        == allocation.aus@[new_idx] as nat);
                                    assert(added.contains(au));
                                    assert(allocation.as_set().contains(au));
                                    assert(false);
                                }
                            }
                        }
                    }
                    if old(self).bounded(total_aus) {
                        assert forall |i: int| 0 <= i < self.allocators@.len()
                            implies {
                                &&& 0 < #[trigger] self.allocators@[i].alloc_au_nat()
                                &&& self.allocators@[i].alloc_au_nat() < (total_aus as nat)
                            } by {
                            if i == active_post_idx {
                                assert(self.allocators@[i] == active);
                                assert(active == pre_allocators[pre_allocators.len() - 1]);
                                assert(old(self).bounded(total_aus));
                            } else if i < prefix_len {
                                assert(self.allocators@[i] == pre_allocators[i]);
                                assert(old(self).bounded(total_aus));
                            } else {
                                let new_idx = i - prefix_len;
                                assert(0 <= new_idx < allocation.aus@.len());
                                assert(self.allocators@[i] == before_active_push[i]);
                                assert(before_active_push[prefix_len + new_idx].alloc_au_nat()
                                    == allocation.aus@[new_idx] as nat);
                                assert(allocation.wf(total_aus));
                                assert(AuAllocation::vec_matches_run(allocation.aus@, allocation.run));
                                assert(allocation.run.wf(total_aus));
                                assert((allocation.aus@[new_idx] as nat)
                                    == (allocation.run.start as nat) + (new_idx as nat));
                                assert((allocation.run.start as nat)
                                    <= (allocation.aus@[new_idx] as nat));
                                assert((allocation.aus@[new_idx] as nat)
                                    < (allocation.run.end as nat)) by {
                                    assert(allocation.aus@.len() == allocation.run.len());
                                    assert(new_idx < allocation.aus@.len());
                                    assert(allocation.run.len()
                                        == ((allocation.run.end as int)
                                            - (allocation.run.start as int)) as nat);
                                }
                            }
                        }
                        assert(self.bounded(total_aus));
                    }
                }
                Some(allocation)
            },
        }
    }

    pub fn refill_from_pool_allow_empty(
        &mut self,
        pool: &mut AuPoolImpl,
        total_aus: IAU,
    ) -> (out: Option<AuAllocation>)
        requires
            old(self).wf(),
            Self::allocators_unique(old(self).allocators@),
            old(pool).canonical_wf(total_aus),
            old(pool)@.disjoint(Self::allocators_au_set(old(self).allocators@)),
        ensures
            self.wf(),
            Self::allocators_unique(self.allocators@),
            pool.canonical_wf(total_aus),
            pool@.disjoint(Self::allocators_au_set(self.allocators@)),
            self.threshold() == old(self).threshold(),
            old(self).allocation_ready() ==> self.allocation_ready(),
            old(self).allocation_ready() ==> self.alloc_au() == old(self).alloc_au(),
            old(self).allocation_ready() ==> self.alloc_au_nat() == old(self).alloc_au_nat(),
            old(self).allocation_ready() ==> self.next_page() == old(self).next_page(),
            old(self).bounded(total_aus) ==> self.bounded(total_aus),
            match out {
                Some(allocation) => {
                    &&& allocation.wf(total_aus)
                    &&& allocation.as_set() <= old(pool)@
                    &&& pool@ =~= old(pool)@ - allocation.as_set()
                    &&& self.i() == old(self).i().add_aus(allocation.as_set())
                },
                None => {
                    &&& *self == *old(self)
                    &&& *pool == *old(pool)
                },
            },
    {
        if self.is_allocation_ready() {
            self.refill_from_pool(pool, total_aus)
        } else {
            proof {
                assert(self.wf());
                assert(self.allocators@.len() == 0);
                assert(Self::allocators_au_set(self.allocators@) =~= Set::<AU>::empty()) by {
                    assert forall |au: AU|
                        #[trigger] Self::allocators_au_set(self.allocators@).contains(au)
                        implies false by {
                        let idx = choose |i: int| 0 <= i < self.allocators@.len()
                            && #[trigger] self.allocators@[i].alloc_au_nat() == au;
                        assert(false);
                    }
                }
            }
            let free_count = self.free_au_count();
            if free_count >= self.free_au_threshold {
                proof {
                    assert(pool@ =~= old(pool)@);
                    assert(self.i() == old(self).i());
                    assert(self.allocators@ == old(self).allocators@);
                    assert(self.curr == old(self).curr);
                    assert(self.free_au_threshold == old(self).free_au_threshold);
                }
                return None;
            }

            let needed = self.free_au_threshold - free_count;
            proof {
                assert((free_count as nat) < (self.free_au_threshold as nat));
                assert(0 < (needed as nat));
            }
            match pool.alloc(total_aus, needed) {
                None => {
                    proof {
                        assert(self.i() == old(self).i());
                        assert(self.allocators@ == old(self).allocators@);
                        assert(self.curr == old(self).curr);
                        assert(self.free_au_threshold == old(self).free_au_threshold);
                    }
                    None
                },
                Some(allocation) => {
                    let aus = allocation.aus.clone();
                    proof {
                        au_allocation_vec_unique(allocation, total_aus);
                        au_allocation_vec_set_matches(allocation, total_aus);
                        assert(aus@ == allocation.aus@);
                        assert(iau_vec_set(aus@) =~= allocation.as_set());
                        assert(iau_vec_set(aus@).disjoint(
                            Self::allocators_au_set(self.allocators@),
                        )) by {
                            assert(Self::allocators_au_set(self.allocators@) =~= Set::<AU>::empty());
                        }
                    }
                    self.add_aus(aus);
                    proof {
                        assert(self.threshold() == old(self).threshold());
                        assert(self.i() == old(self).i().add_aus(allocation.as_set()));
                        assert(pool@.disjoint(Self::allocators_au_set(self.allocators@))) by {
                            assert(pool@ =~= old(pool)@ - allocation.as_set());
                            assert(Self::allocators_au_set(self.allocators@)
                                =~= Self::allocators_au_set(old(self).allocators@)
                                    + allocation.as_set());
                            assert forall |au: AU| #[trigger] pool@.contains(au)
                                implies !Self::allocators_au_set(self.allocators@).contains(au) by {
                                assert(!allocation.as_set().contains(au));
                                if Self::allocators_au_set(self.allocators@).contains(au) {
                                    if Self::allocators_au_set(old(self).allocators@).contains(au) {
                                        assert(old(pool)@.disjoint(
                                            Self::allocators_au_set(old(self).allocators@),
                                        ));
                                        assert(false);
                                    } else {
                                        assert(allocation.as_set().contains(au));
                                        assert(false);
                                    }
                                }
                            }
                        }
                    }
                    Some(allocation)
                },
            }
        }
    }
}

} // verus!
