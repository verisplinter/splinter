// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;

use crate::allocation_layer::MiniAllocator_v::{
    MiniAllocator as SpecMiniAllocator, PageAllocator as SpecMiniPageAllocator,
};
use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::AuPoolImpl_v::{AuAllocation, AuPoolImpl};
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::implementation::PageAllocator_v::PageAllocator;
use crate::spec::ImplDisk_t::{IAddress, IAU, IPage};

verus! {

pub struct MiniAllocatorImpl {
    pub allocators: Vec<PageAllocator>,
    pub free_au_threshold: IAU,
}

impl MiniAllocatorImpl {
    pub open spec fn allocators_wf(allocators: Seq<PageAllocator>) -> bool
    {
        forall |i: int| 0 <= i < allocators.len() ==> #[trigger] allocators[i].wf()
    }

    pub open spec fn wf(&self) -> bool
    {
        &&& Self::allocators_wf(self.allocators@)
    }

    pub open spec fn allocation_ready(&self) -> bool
    {
        &&& self.wf()
        &&& 0 < self.allocators@.len()
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

    pub open spec fn page_allocator_reserved(allocator: PageAllocator) -> Set<Address>
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
            observed: Set::empty(),
            reserved: Self::page_allocator_reserved(allocator),
            au: allocator.alloc_au_nat(),
        }
    }

    pub open spec fn i(&self) -> SpecMiniAllocator
    {
        let allocators = self.allocators@;
        let allocs = Map::new(
            |au: AU| exists |idx: int|
                0 <= idx < allocators.len() && allocators[idx].alloc_au_nat() == au,
            |au: AU| {
                let idx = choose |idx: int|
                    0 <= idx < allocators.len() && allocators[idx].alloc_au_nat() == au;
                Self::page_allocator_i(allocators[idx])
            },
        );
        let curr = if allocators.len() > 0 {
            Some(allocators[allocators.len() - 1].alloc_au_nat())
        } else {
            None
        };
        SpecMiniAllocator { allocs, curr }
    }

    pub fn empty(free_au_threshold: IAU) -> (out: Self)
        ensures
            out.wf(),
            !out.allocation_ready(),
            out.threshold() == free_au_threshold,
    {
        Self { allocators: Vec::new(), free_au_threshold }
    }

    pub fn new(alloc_au: IAU, start_page: IPage, free_au_threshold: IAU) -> (out: Self)
        ensures
            out.wf(),
            out.allocation_ready(),
            out.alloc_au() == alloc_au,
            out.alloc_au_nat() == alloc_au as nat,
            out.next_page() == start_page,
            out.threshold() == free_au_threshold,
    {
        let mut allocators = Vec::<PageAllocator>::new();
        allocators.push(PageAllocator::new(alloc_au, start_page));
        let out = Self { allocators, free_au_threshold };
        proof {
            assert(out.allocators@.len() == 1);
            assert(out.allocators@[0].wf());
            assert(out.wf());
            assert(out.active_allocator().alloc_au() == alloc_au);
            assert(out.active_allocator().next_page() == start_page);
        }
        out
    }

    pub fn reset_threshold(&mut self, free_au_threshold: IAU)
        requires
            old(self).wf(),
        ensures
            self.wf(),
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

    pub fn peek_next_addr(&self) -> (out: IAddress)
        requires
            self.allocation_ready(),
        ensures
            out.au == self.alloc_au(),
            out.page == self.next_page(),
            out@.au == self.alloc_au_nat(),
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
            self.allocation_ready(),
            self.alloc_au() == old(self).alloc_au(),
            self.alloc_au_nat() == old(self).alloc_au_nat(),
            self.next_page() == old(self).next_page() + 1,
            self.threshold() == old(self).threshold(),
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
            assert(self.wf());
            assert(self.active_allocator() == post_active);
            assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
            assert(post_active.alloc_au() == pre_allocators[pre_allocators.len() - 1].alloc_au());
            assert(post_active.next_page() == pre_allocators[pre_allocators.len() - 1].next_page() + 1);
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
            out is None ==> !old(self).allocation_ready(),
    {
        if self.allocators.len() == 0 {
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
                assert(self.wf());
                assert(self.allocation_ready());
                assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
                assert(out.au == old(self).alloc_au());
                assert(out.page == old(self).next_page());
            }
            Some(out)
        }
    }

    pub fn add_aus(&mut self, aus: Vec<IAU>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.threshold() == old(self).threshold(),
    {
        let saved_threshold = self.free_au_threshold;
        let mut idx: usize = 0;
        while idx < aus.len()
            invariant
                idx <= aus.len(),
                Self::allocators_wf(self.allocators@),
                self.free_au_threshold == saved_threshold,
            decreases aus.len() - idx
        {
            let ghost pre_allocators = self.allocators@;
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
            }
            idx = idx + 1;
        }
        proof {
            assert(self.wf());
            assert(self.free_au_threshold == saved_threshold);
        }
    }

    pub fn refill_from_pool(
        &mut self,
        pool: &mut AuPoolImpl,
        total_aus: IAU,
    ) -> (out: Option<AuAllocation>)
        requires
            old(self).allocation_ready(),
            old(pool).canonical_wf(total_aus),
        ensures
            self.wf(),
            self.allocation_ready(),
            self.alloc_au() == old(self).alloc_au(),
            self.alloc_au_nat() == old(self).alloc_au_nat(),
            self.next_page() == old(self).next_page(),
            pool.canonical_wf(total_aus),
            self.threshold() == old(self).threshold(),
            match out {
                Some(allocation) => {
                    &&& allocation.wf(total_aus)
                    &&& allocation.as_set() <= old(pool)@
                    &&& pool@ =~= old(pool)@ - allocation.as_set()
                },
                None => pool@ =~= old(pool)@,
            },
    {
        let saved_threshold = self.free_au_threshold;
        let free_count = self.free_au_count();
        if free_count >= self.free_au_threshold {
            proof {
                assert(self.free_au_threshold == saved_threshold);
                assert(pool@ =~= old(pool)@);
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
                let ghost pre_allocators = self.allocators@;
                let active = self.allocators.pop().unwrap();
                proof {
                    assert(active == pre_allocators[pre_allocators.len() - 1]);
                    assert(self.allocators@ == pre_allocators.drop_last());
                    assert forall |i: int| 0 <= i < self.allocators@.len()
                        implies #[trigger] self.allocators@[i].wf() by {
                        assert(self.allocators@[i] == pre_allocators[i]);
                        assert(pre_allocators[i].wf());
                    }
                }

                let mut idx: usize = 0;
                while idx < allocation.aus.len()
                    invariant
                        idx <= allocation.aus.len(),
                        Self::allocators_wf(self.allocators@),
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
                    }
                    idx = idx + 1;
                }

                let ghost before_active_push = self.allocators@;
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
                    assert(self.wf());
                    assert(self.allocation_ready());
                    assert(self.active_allocator() == active);
                    assert(old(self).active_allocator() == pre_allocators[pre_allocators.len() - 1]);
                    assert(active == old(self).active_allocator());
                    assert(self.alloc_au() == old(self).alloc_au());
                    assert(self.alloc_au_nat() == old(self).alloc_au_nat());
                    assert(self.next_page() == old(self).next_page());
                    assert(self.free_au_threshold == saved_threshold);
                }
                Some(allocation)
            },
        }
    }
}

} // verus!
