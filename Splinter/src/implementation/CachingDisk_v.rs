// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Infinite cache backed by a forgettable persistent map.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use verus_state_machines_macros::state_machine;

use crate::disk::GenericDisk_v::AU;
use crate::spec::AsyncDisk_t::{Address, RawPage};

verus!{

pub type CachingDiskRawPage = RawPage;

pub enum PageStatus {
    Dirty,
    Writeback,
    Clean,
}

pub open spec fn addresses_in_aus(aus: Set<AU>) -> Set<Address> {
    Set::new(|addr: Address| aus.contains(addr.au))
}

pub open spec fn status_map(addrs: Set<Address>, status: PageStatus) -> Map<Address, PageStatus> {
    Map::new(|addr| addrs.contains(addr), |addr| status)
}

state_machine!{ CachingDisk {
    fields {
        pub cache: Map<Address, RawPage>,
        pub persistent: Map<Address, RawPage>,
        pub status: Map<Address, PageStatus>,
    }

    pub enum Label {
        Access{reads: Map<Address, RawPage>, writes: Map<Address, RawPage>},
        ObserveCleanAUs{aus: Set<AU>},
        Forget{aus: Set<AU>},
        Internal{},
    }

    pub open spec fn visible(self) -> Map<Address, RawPage> {
        self.persistent.union_prefer_right(self.cache)
    }

    pub open spec fn persistent_visible_agree_on(self, addrs: Set<Address>) -> bool {
        self.persistent.restrict(addrs) == self.visible().restrict(addrs)
    }

    pub open spec fn all_status(self, addrs: Set<Address>, page_status: PageStatus) -> bool {
        forall |addr: Address| #[trigger] addrs.contains(addr) ==> {
            &&& self.status.contains_key(addr)
            &&& self.status[addr] == page_status
        }
    }

    pub open spec fn all_cleanable(self, addrs: Set<Address>) -> bool {
        forall |addr: Address| #[trigger] addrs.contains(addr) ==> {
            &&& self.status.contains_key(addr)
            &&& (self.status[addr] == PageStatus::Writeback || self.status[addr] == PageStatus::Clean)
        }
    }

    pub open spec fn persisted(self, addrs: Set<Address>) -> bool {
        forall |addr: Address| #[trigger] addrs.contains(addr) && self.status[addr] == PageStatus::Writeback ==> {
                &&& self.cache.contains_key(addr)
                &&& self.persistent.contains_key(addr)
                &&& self.persistent[addr] == self.cache[addr]
        }
    }

    pub open spec fn aus_clean_or_evictable(self, aus: Set<AU>) -> bool {
        forall |addr: Address| #[trigger] self.cache.contains_key(addr) && aus.contains(addr.au) ==> {
            &&& self.status.contains_key(addr)
            &&& self.status[addr] == PageStatus::Clean
        }
    }

    pub open spec fn addrs_clean_or_evictable(self, addrs: Set<Address>) -> bool {
        forall |addr: Address| #[trigger] self.cache.contains_key(addr) && addrs.contains(addr) ==> {
            &&& self.status.contains_key(addr)
            &&& self.status[addr] == PageStatus::Clean
        }
    }

    init!{ initialize() {
        init cache = Map::<Address, RawPage>::empty();
        init persistent = Map::<Address, RawPage>::empty();
        init status = Map::<Address, PageStatus>::empty();
    }}

    transition!{ load(lbl: Label, addrs: Set<Address>) {
        require lbl is Internal;
        require addrs.disjoint(pre.cache.dom());
        require addrs <= pre.persistent.dom();

        let loaded = pre.persistent.restrict(addrs);
        let status_updates = status_map(addrs, PageStatus::Clean);

        update cache = pre.cache.union_prefer_right(loaded);
        update status = pre.status.union_prefer_right(status_updates);
    }}

    transition!{ access(lbl: Label) {
        require let Label::Access{reads, writes} = lbl;
        require reads <= pre.cache;
        require forall |addr: Address| #[trigger] writes.contains_key(addr) && pre.status.contains_key(addr)
            ==> !(pre.status[addr] == PageStatus::Writeback);

        let status_updates = status_map(writes.dom(), PageStatus::Dirty);

        update cache = pre.cache.union_prefer_right(writes);
        update status = pre.status.union_prefer_right(status_updates);
    }}

    transition!{ begin_writeback(lbl: Label, addrs: Set<Address>) {
        require lbl is Internal;
        require pre.all_status(addrs, PageStatus::Dirty);

        let status_updates = status_map(addrs, PageStatus::Writeback);

        update status = pre.status.union_prefer_right(status_updates);
    }}

    transition!{ persist_writeback(lbl: Label, addrs: Set<Address>) {
        require lbl is Internal;
        require pre.all_status(addrs, PageStatus::Writeback);

        update persistent = pre.persistent.union_prefer_right(pre.cache.restrict(addrs));
    }}

    transition!{ mark_clean(lbl: Label, addrs: Set<Address>) {
        require lbl is Internal;
        require addrs <= pre.cache.dom();
        require pre.all_cleanable(addrs);
        require pre.persisted(addrs);

        let status_updates = status_map(addrs, PageStatus::Clean);

        update status = pre.status.union_prefer_right(status_updates);
    }}

    transition!{ observe_clean_aus(lbl: Label) {
        require let Label::ObserveCleanAUs{aus} = lbl;
        require pre.aus_clean_or_evictable(aus);
    }}

    transition!{ evict_clean(lbl: Label, addrs: Set<Address>) {
        require lbl is Internal;
        require pre.all_status(addrs, PageStatus::Clean);

        update cache = pre.cache.remove_keys(addrs);
        update status = pre.status.remove_keys(addrs);
    }}

    transition!{ forget(lbl: Label) {
        require let Label::Forget{aus} = lbl;
        let addrs = addresses_in_aus(aus);

        update cache = pre.cache.remove_keys(addrs);
        update persistent = pre.persistent.remove_keys(addrs);
        update status = pre.status.remove_keys(addrs);
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl is Internal;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.status.dom() =~= self.cache.dom()
        &&& forall |addr: Address| #[trigger] self.status.contains_key(addr)
            && self.status[addr] == PageStatus::Clean ==> {
                &&& self.persistent.contains_key(addr)
                &&& self.persistent[addr] == self.cache[addr]
            }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {}

    #[inductive(load)]
    fn load_inductive(pre: Self, post: Self, lbl: Label, addrs: Set<Address>) {
        reveal(CachingDisk::State::load);
        assert(lbl is Internal);
        assert(addrs <= pre.persistent.dom());
        assert(post.status.dom() =~= post.cache.dom()) by {
            assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                implies post.cache.dom().contains(addr) by {
                if addrs.contains(addr) {
                    assert(pre.persistent.contains_key(addr));
                    assert(pre.persistent.restrict(addrs).contains_key(addr));
                } else {
                    assert(pre.status.dom().contains(addr));
                    assert(pre.cache.dom().contains(addr));
                }
            }
            assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                implies post.status.dom().contains(addr) by {
                if pre.persistent.restrict(addrs).contains_key(addr) {
                    assert(addrs.contains(addr));
                } else {
                    assert(pre.cache.dom().contains(addr));
                    assert(pre.status.dom().contains(addr));
                }
            }
        };
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            if addrs.contains(addr) {
                assert(pre.persistent.contains_key(addr));
                assert(pre.persistent.restrict(addrs).contains_key(addr));
                assert(post.persistent[addr] == post.cache[addr]);
            } else {
                assert(pre.status.contains_key(addr));
                assert(pre.status[addr] == PageStatus::Clean);
            }
        }
    }

    #[inductive(access)]
    fn access_inductive(pre: Self, post: Self, lbl: Label) {
        let writes = lbl.arrow_Access_writes();
        assert(post.status.dom() =~= post.cache.dom()) by {
            assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                implies post.cache.dom().contains(addr) by {
                if writes.contains_key(addr) {
                } else {
                    assert(pre.status.dom().contains(addr));
                    assert(pre.cache.dom().contains(addr));
                }
            }
            assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                implies post.status.dom().contains(addr) by {
                if writes.contains_key(addr) {
                } else {
                    assert(pre.cache.dom().contains(addr));
                    assert(pre.status.dom().contains(addr));
                }
            }
        };
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            if writes.contains_key(addr) {
                assert(post.status[addr] == PageStatus::Dirty);
                assert(false);
            } else {
                assert(pre.status.contains_key(addr));
                assert(pre.status[addr] == PageStatus::Clean);
            }
        }
    }

    #[inductive(begin_writeback)]
    fn begin_writeback_inductive(pre: Self, post: Self, lbl: Label, addrs: Set<Address>) {
        assert(post.status.dom() =~= post.cache.dom()) by {
            assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                implies post.cache.dom().contains(addr) by {
                assert(pre.status.dom().contains(addr));
                assert(pre.cache.dom().contains(addr));
            }
            assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                implies post.status.dom().contains(addr) by {
                assert(pre.cache.dom().contains(addr));
                assert(pre.status.dom().contains(addr));
            }
        };
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            if addrs.contains(addr) {
                assert(post.status[addr] == PageStatus::Writeback);
                assert(false);
            } else {
                assert(pre.status.contains_key(addr));
                assert(pre.status[addr] == PageStatus::Clean);
            }
        }
    }

    #[inductive(persist_writeback)]
    fn persist_writeback_inductive(pre: Self, post: Self, lbl: Label, addrs: Set<Address>) {
        assert(post.status.dom() =~= post.cache.dom());
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            assert(pre.status.contains_key(addr));
            assert(pre.status[addr] == PageStatus::Clean);
        }
    }

    #[inductive(mark_clean)]
    fn mark_clean_inductive(pre: Self, post: Self, lbl: Label, addrs: Set<Address>) {
        assert(post.status.dom() =~= post.cache.dom()) by {
            assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                implies post.cache.dom().contains(addr) by {
                assert(pre.status.dom().contains(addr));
                assert(pre.cache.dom().contains(addr));
            }
            assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                implies post.status.dom().contains(addr) by {
                assert(pre.cache.dom().contains(addr));
                assert(pre.status.dom().contains(addr));
            }
        };
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            if addrs.contains(addr) {
                assert(pre.persisted(addrs));
                assert(pre.all_cleanable(addrs));
                if pre.status[addr] == PageStatus::Clean {
                    assert(pre.persistent.contains_key(addr));
                    assert(pre.persistent[addr] == pre.cache[addr]);
                } else {
                    assert(pre.status[addr] == PageStatus::Writeback);
                }
            } else {
                assert(pre.status.contains_key(addr));
                assert(pre.status[addr] == PageStatus::Clean);
            }
        }
    }

    #[inductive(observe_clean_aus)]
    fn observe_clean_aus_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(evict_clean)]
    fn evict_clean_inductive(pre: Self, post: Self, lbl: Label, addrs: Set<Address>) {
        assert(post.status.dom() =~= post.cache.dom()) by {
            assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                implies post.cache.dom().contains(addr) by {
                assert(pre.status.dom().contains(addr));
                assert(pre.cache.dom().contains(addr));
            }
            assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                implies post.status.dom().contains(addr) by {
                assert(pre.cache.dom().contains(addr));
                assert(pre.status.dom().contains(addr));
            }
        };
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            assert(pre.status.contains_key(addr));
            assert(pre.status[addr] == PageStatus::Clean);
        }
    }

    #[inductive(forget)]
    fn forget_inductive(pre: Self, post: Self, lbl: Label) {
        let addrs = addresses_in_aus(lbl.arrow_Forget_aus());
        assert(post.status.dom() =~= post.cache.dom()) by {
            assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                implies post.cache.dom().contains(addr) by {
                assert(pre.status.dom().contains(addr));
                assert(pre.cache.dom().contains(addr));
            }
            assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                implies post.status.dom().contains(addr) by {
                assert(pre.cache.dom().contains(addr));
                assert(pre.status.dom().contains(addr));
            }
        };
        assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
            && post.status[addr] == PageStatus::Clean implies {
                &&& post.persistent.contains_key(addr)
                &&& post.persistent[addr] == post.cache[addr]
            } by {
            assert(pre.status.contains_key(addr));
            assert(pre.status[addr] == PageStatus::Clean);
        }
    }

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {}

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CachingDisk::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);

        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::load(addrs) => {
                assert(CachingDisk::State::load(pre, post, lbl, addrs)) by {
                    reveal(CachingDisk::State::load);
                }
                CachingDisk::State::load_inductive(pre, post, lbl, addrs);
            },
            CachingDisk::Step::access() => {
                reveal(CachingDisk::State::access);
                assert(CachingDisk::State::access(pre, post, lbl));
                let writes = lbl.arrow_Access_writes();
                assert(post.status.dom() =~= post.cache.dom()) by {
                    assert forall |addr: Address| #[trigger] post.status.dom().contains(addr)
                        implies post.cache.dom().contains(addr) by {
                        if writes.contains_key(addr) {
                        } else {
                            assert(pre.status.dom().contains(addr));
                            assert(pre.cache.dom().contains(addr));
                        }
                    }
                    assert forall |addr: Address| #[trigger] post.cache.dom().contains(addr)
                        implies post.status.dom().contains(addr) by {
                        if writes.contains_key(addr) {
                        } else {
                            assert(pre.cache.dom().contains(addr));
                            assert(pre.status.dom().contains(addr));
                        }
                    }
                };
                assert forall |addr: Address| #[trigger] post.status.contains_key(addr)
                    && post.status[addr] == PageStatus::Clean implies {
                        &&& post.persistent.contains_key(addr)
                        &&& post.persistent[addr] == post.cache[addr]
                    } by {
                    if writes.contains_key(addr) {
                        assert(post.status[addr] == PageStatus::Dirty);
                        assert(false);
                    } else {
                        assert(pre.status.contains_key(addr));
                        assert(pre.status[addr] == PageStatus::Clean);
                    }
                }
            },
            CachingDisk::Step::begin_writeback(addrs) => {
                CachingDisk::State::begin_writeback_inductive(pre, post, lbl, addrs);
            },
            CachingDisk::Step::persist_writeback(addrs) => {
                CachingDisk::State::persist_writeback_inductive(pre, post, lbl, addrs);
            },
            CachingDisk::Step::mark_clean(addrs) => {
                CachingDisk::State::mark_clean_inductive(pre, post, lbl, addrs);
            },
            CachingDisk::Step::observe_clean_aus() => {
                CachingDisk::State::observe_clean_aus_inductive(pre, post, lbl);
            },
            CachingDisk::Step::evict_clean(addrs) => {
                CachingDisk::State::evict_clean_inductive(pre, post, lbl, addrs);
            },
            CachingDisk::Step::forget() => {
                CachingDisk::State::forget_inductive(pre, post, lbl);
            },
            CachingDisk::Step::internal_noop() => {
                CachingDisk::State::internal_noop_inductive(pre, post, lbl);
            },
            _ => {
                assert(post.inv());
            },
        }
    }
}}

impl CachingDisk::State {
    pub proof fn load_effect(pre: Self, post: Self, addrs: Set<Address>)
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::load(addrs),
            ),
        ensures
            addrs.disjoint(pre.cache.dom()),
            forall |addr: Address| #[trigger] addrs.contains(addr) ==> pre.persistent.contains_key(addr),
            post.cache == pre.cache.union_prefer_right(pre.persistent.restrict(addrs)),
            post.persistent == pre.persistent,
            post.status == pre.status.union_prefer_right(status_map(addrs, PageStatus::Clean)),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        assert(CachingDisk::State::load(pre, post, lbl, addrs));
        assert(addrs <= pre.persistent.dom());
        assert forall |addr: Address| #[trigger] addrs.contains(addr)
            implies pre.persistent.contains_key(addr) by {
        }
    }

    pub proof fn access_effect(pre: Self, post: Self, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>)
        requires
            CachingDisk::State::next(
                pre,
                post,
                CachingDisk::Label::Access{reads, writes},
            ),
        ensures
            reads <= pre.cache,
            post.cache == pre.cache.union_prefer_right(writes),
            post.persistent == pre.persistent,
            post.status == pre.status.union_prefer_right(status_map(writes.dom(), PageStatus::Dirty)),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Access{reads, writes};
        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::access() => {
                reveal(CachingDisk::State::access);
                assert(CachingDisk::State::access(pre, post, lbl));
            },
            _ => { assert(false); },
        }
    }

    pub proof fn access_visible_effect(pre: Self, post: Self, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>)
        requires
            CachingDisk::State::next(
                pre,
                post,
                CachingDisk::Label::Access{reads, writes},
            ),
        ensures
            reads <= pre.cache,
            post.visible() == pre.visible().union_prefer_right(writes),
    {
        Self::access_effect(pre, post, reads, writes);
        assert_maps_equal!(post.visible(), pre.visible().union_prefer_right(writes), addr => {
            if writes.contains_key(addr) {
            } else if pre.cache.contains_key(addr) {
            } else {
            }
        });
    }

    pub proof fn begin_writeback_effect(pre: Self, post: Self, addrs: Set<Address>)
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::begin_writeback(addrs),
            ),
        ensures
            pre.all_status(addrs, PageStatus::Dirty),
            post.cache == pre.cache,
            post.persistent == pre.persistent,
            post.status == pre.status.union_prefer_right(status_map(addrs, PageStatus::Writeback)),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        assert(CachingDisk::State::begin_writeback(pre, post, lbl, addrs));
    }

    pub proof fn persist_writeback_effect(pre: Self, post: Self, addrs: Set<Address>)
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::persist_writeback(addrs),
            ),
        ensures
            pre.all_status(addrs, PageStatus::Writeback),
            post.cache == pre.cache,
            post.persistent == pre.persistent.union_prefer_right(pre.cache.restrict(addrs)),
            post.status == pre.status,
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        assert(CachingDisk::State::persist_writeback(pre, post, lbl, addrs));
    }

    pub proof fn mark_clean_effect(
        pre: Self,
        post: Self,
        addrs: Set<Address>,
    )
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::mark_clean(addrs),
            ),
        ensures
            addrs <= pre.cache.dom(),
            pre.all_cleanable(addrs),
            pre.persisted(addrs),
            post.cache == pre.cache,
            post.persistent == pre.persistent,
            post.status == pre.status.union_prefer_right(status_map(addrs, PageStatus::Clean)),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        assert(CachingDisk::State::mark_clean(pre, post, lbl, addrs));
    }

    pub proof fn evict_clean_effect(pre: Self, post: Self, addrs: Set<Address>)
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::evict_clean(addrs),
            ),
        ensures
            pre.all_status(addrs, PageStatus::Clean),
            post.cache == pre.cache.remove_keys(addrs),
            post.persistent == pre.persistent,
            post.status == pre.status.remove_keys(addrs),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        assert(CachingDisk::State::evict_clean(pre, post, lbl, addrs));
    }

    pub proof fn forget_effect(pre: Self, post: Self, aus: Set<AU>)
        requires
            CachingDisk::State::next(
                pre,
                post,
                CachingDisk::Label::Forget{aus},
            ),
        ensures
            post.cache == pre.cache.remove_keys(addresses_in_aus(aus)),
            post.persistent == pre.persistent.remove_keys(addresses_in_aus(aus)),
            post.status == pre.status.remove_keys(addresses_in_aus(aus)),
            post.visible() == pre.visible().remove_keys(addresses_in_aus(aus)),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Forget{aus};
        let addrs = addresses_in_aus(aus);
        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::forget() => {},
            _ => { assert(false); },
        }
        assert_maps_equal!(post.visible(), pre.visible().remove_keys(addrs), addr => {
            if addrs.contains(addr) {
            } else if pre.cache.contains_key(addr) {
            } else {
            }
        });
    }

    pub proof fn load_visible_unchanged(pre: Self, post: Self, addrs: Set<Address>)
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::load(addrs),
            ),
        ensures
            post.visible() == pre.visible(),
    {
        Self::load_effect(pre, post, addrs);
        assert_maps_equal!(post.visible(), pre.visible(), addr => {
            if addrs.contains(addr) {
                assert(!pre.cache.contains_key(addr));
                assert(pre.persistent.contains_key(addr));
            }
        });
    }

    pub proof fn begin_writeback_visible_unchanged(pre: Self, post: Self, addrs: Set<Address>)
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::begin_writeback(addrs),
            ),
        ensures
            post.visible() == pre.visible(),
    {
        Self::begin_writeback_effect(pre, post, addrs);
        assert_maps_equal!(post.visible(), pre.visible());
    }

    pub proof fn persist_writeback_visible_unchanged(pre: Self, post: Self, addrs: Set<Address>)
        requires
            pre.inv(),
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::persist_writeback(addrs),
            ),
        ensures
            post.visible() == pre.visible(),
    {
        Self::persist_writeback_effect(pre, post, addrs);
        assert_maps_equal!(post.visible(), pre.visible(), addr => {
            if pre.cache.contains_key(addr) {
                assert(post.cache.contains_key(addr));
            } else {
                if pre.cache.restrict(addrs).contains_key(addr) {
                    assert(addrs.contains(addr));
                    assert(pre.all_status(addrs, PageStatus::Writeback));
                    assert(pre.status.contains_key(addr));
                    assert(pre.status.dom().contains(addr));
                    assert(pre.cache.dom().contains(addr));
                    assert(false);
                }
            }
        });
    }

    pub proof fn mark_clean_visible_unchanged(
        pre: Self,
        post: Self,
        addrs: Set<Address>,
    )
        requires
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::mark_clean(addrs),
            ),
        ensures
            post.visible() == pre.visible(),
    {
        Self::mark_clean_effect(pre, post, addrs);
        assert_maps_equal!(post.visible(), pre.visible());
    }

    pub proof fn evict_clean_visible_unchanged(pre: Self, post: Self, addrs: Set<Address>)
        requires
            pre.inv(),
            CachingDisk::State::next_by(
                pre,
                post,
                CachingDisk::Label::Internal{},
                CachingDisk::Step::evict_clean(addrs),
            ),
        ensures
            post.visible() == pre.visible(),
    {
        Self::evict_clean_effect(pre, post, addrs);
        assert_maps_equal!(post.visible(), pre.visible(), addr => {
            if addrs.contains(addr) {
                assert(pre.all_status(addrs, PageStatus::Clean));
                assert(pre.status.contains_key(addr));
                assert(pre.status[addr] == PageStatus::Clean);
                assert(pre.persistent.contains_key(addr));
                assert(pre.persistent[addr] == pre.cache[addr]);
            }
        });
    }

    pub proof fn internal_visible_unchanged(pre: Self, post: Self)
        requires
            pre.inv(),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Internal{}),
        ensures
            post.visible() == pre.visible(),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::load(addrs) => {
                Self::load_visible_unchanged(pre, post, addrs);
            },
            CachingDisk::Step::begin_writeback(addrs) => {
                Self::begin_writeback_visible_unchanged(pre, post, addrs);
            },
            CachingDisk::Step::persist_writeback(addrs) => {
                Self::persist_writeback_visible_unchanged(pre, post, addrs);
            },
            CachingDisk::Step::mark_clean(addrs) => {
                Self::mark_clean_visible_unchanged(pre, post, addrs);
            },
            CachingDisk::Step::evict_clean(addrs) => {
                Self::evict_clean_visible_unchanged(pre, post, addrs);
            },
            CachingDisk::Step::internal_noop() => {
                assert(post == pre);
                assert_maps_equal!(post.visible(), pre.visible());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_preserves_persistent_visible_agree_on(
        pre: Self,
        post: Self,
        addrs: Set<Address>,
    )
        requires
            pre.inv(),
            post.inv(),
            pre.persistent_visible_agree_on(addrs),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Internal{}),
        ensures
            post.persistent_visible_agree_on(addrs),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::load(loaded_addrs) => {
                Self::load_visible_unchanged(pre, post, loaded_addrs);
            },
            CachingDisk::Step::begin_writeback(writeback_addrs) => {
                Self::begin_writeback_visible_unchanged(pre, post, writeback_addrs);
            },
            CachingDisk::Step::persist_writeback(persist_addrs) => {
                Self::persist_writeback_visible_unchanged(pre, post, persist_addrs);
            },
            CachingDisk::Step::mark_clean(clean_addrs) => {
                Self::mark_clean_visible_unchanged(pre, post, clean_addrs);
            },
            CachingDisk::Step::evict_clean(evict_addrs) => {
                Self::evict_clean_visible_unchanged(pre, post, evict_addrs);
            },
            CachingDisk::Step::internal_noop() => {
                assert(post == pre);
                assert_maps_equal!(post.visible(), pre.visible());
            },
            _ => {
                assert(false);
            },
        }

        assert_maps_equal!(
            post.persistent.restrict(addrs),
            post.visible().restrict(addrs),
            addr => {
                if addrs.contains(addr) {
                    assert(pre.persistent.restrict(addrs)
                        == pre.visible().restrict(addrs));
                    match step {
                        CachingDisk::Step::persist_writeback(persist_addrs) => {
                            Self::persist_writeback_effect(pre, post, persist_addrs);
                            if persist_addrs.contains(addr) {
                                assert(pre.all_status(persist_addrs, PageStatus::Writeback));
                                assert(pre.status.contains_key(addr));
                                assert(pre.status[addr] == PageStatus::Writeback);
                                assert(pre.status.dom().contains(addr));
                                assert(pre.cache.dom().contains(addr));
                                assert(pre.cache.contains_key(addr));
                                assert(post.persistent.contains_key(addr));
                                assert(post.persistent[addr] == pre.cache[addr]);
                                assert(pre.visible().contains_key(addr));
                                assert(pre.visible()[addr] == pre.cache[addr]);
                                assert(post.visible() == pre.visible());
                                assert(post.visible()[addr] == pre.visible()[addr]);
                            } else {
                                assert(post.persistent == pre.persistent.union_prefer_right(
                                    pre.cache.restrict(persist_addrs),
                                ));
                                if post.persistent.contains_key(addr) {
                                    assert(pre.persistent.contains_key(addr));
                                    assert(post.persistent[addr] == pre.persistent[addr]);
                                    assert(pre.visible().restrict(addrs).contains_key(addr));
                                    assert(pre.persistent.restrict(addrs).contains_key(addr));
                                    assert(pre.persistent.restrict(addrs)[addr]
                                        == pre.visible().restrict(addrs)[addr]);
                                    assert(pre.persistent.restrict(addrs)[addr]
                                        == pre.persistent[addr]);
                                    assert(pre.visible().restrict(addrs)[addr]
                                        == pre.visible()[addr]);
                                    assert(pre.persistent[addr] == pre.visible()[addr]);
                                    assert(post.visible() == pre.visible());
                                }
                            }
                        },
                        _ => {
                            assert(post.visible() == pre.visible());
                            assert(post.persistent == pre.persistent);
                            if post.persistent.contains_key(addr) {
                                assert(pre.persistent.contains_key(addr));
                                assert(pre.visible().restrict(addrs).contains_key(addr));
                                assert(pre.persistent.restrict(addrs).contains_key(addr));
                                assert(pre.persistent.restrict(addrs)[addr]
                                    == pre.visible().restrict(addrs)[addr]);
                                assert(pre.persistent.restrict(addrs)[addr]
                                    == pre.persistent[addr]);
                                assert(pre.visible().restrict(addrs)[addr]
                                    == pre.visible()[addr]);
                                assert(pre.persistent[addr] == pre.visible()[addr]);
                            }
                        },
                    }
                }
            }
        );
    }

    pub proof fn persistent_visible_agree_on_equal_addrs(
        self,
        addrs: Set<Address>,
        other: Set<Address>,
    )
        requires
            self.persistent_visible_agree_on(addrs),
            other =~= addrs,
        ensures
            self.persistent_visible_agree_on(other),
    {
        assert_maps_equal!(
            self.persistent.restrict(other),
            self.visible().restrict(other),
            addr => {
                if other.contains(addr) {
                    assert(addrs.contains(addr));
                    assert(self.persistent.restrict(addrs)
                        == self.visible().restrict(addrs));
                    if self.persistent.contains_key(addr) {
                        assert(self.persistent.restrict(addrs).contains_key(addr));
                        assert(self.visible().restrict(addrs).contains_key(addr));
                        assert(self.persistent.restrict(addrs)[addr]
                            == self.visible().restrict(addrs)[addr]);
                        assert(self.persistent.restrict(addrs)[addr]
                            == self.persistent[addr]);
                        assert(self.visible().restrict(addrs)[addr]
                            == self.visible()[addr]);
                    }
                    if self.visible().contains_key(addr) {
                        assert(self.visible().restrict(addrs).contains_key(addr));
                        assert(self.persistent.restrict(addrs).contains_key(addr));
                        assert(self.persistent.contains_key(addr));
                    }
                }
            }
        );
    }

    pub proof fn same_views_preserve_persistent_visible_agree_on(
        pre: Self,
        post: Self,
        addrs: Set<Address>,
    )
        requires
            pre.persistent_visible_agree_on(addrs),
            post.persistent.restrict(addrs) == pre.persistent.restrict(addrs),
            post.visible().restrict(addrs) == pre.visible().restrict(addrs),
        ensures
            post.persistent_visible_agree_on(addrs),
    {
        assert(post.persistent.restrict(addrs) == post.visible().restrict(addrs));
    }

    pub proof fn extension_preserves_persistent_visible_agree_on(
        pre: Self,
        post: Self,
        addrs: Set<Address>,
    )
        requires
            pre.persistent_visible_agree_on(addrs),
            pre.cache <= post.cache,
            pre.persistent <= post.persistent,
            (post.cache.dom() - pre.cache.dom()).disjoint(addrs),
            (post.persistent.dom() - pre.persistent.dom()).disjoint(addrs),
        ensures
            post.persistent_visible_agree_on(addrs),
    {
        assert(post.persistent.restrict(addrs) == pre.persistent.restrict(addrs)) by {
            assert_maps_equal!(
                post.persistent.restrict(addrs),
                pre.persistent.restrict(addrs),
                addr => {
                    if addrs.contains(addr) {
                        if post.persistent.contains_key(addr) {
                            assert(pre.persistent.contains_key(addr)) by {
                                if !pre.persistent.contains_key(addr) {
                                    assert((post.persistent.dom() - pre.persistent.dom()).contains(addr));
                                    assert(false);
                                }
                            }
                        }
                    }
                }
            );
        }
        assert(post.visible().restrict(addrs) == pre.visible().restrict(addrs)) by {
            assert_maps_equal!(
                post.visible().restrict(addrs),
                pre.visible().restrict(addrs),
                addr => {
                    if addrs.contains(addr) {
                        if post.cache.contains_key(addr) {
                            assert(pre.cache.contains_key(addr)) by {
                                if !pre.cache.contains_key(addr) {
                                    assert((post.cache.dom() - pre.cache.dom()).contains(addr));
                                    assert(false);
                                }
                            }
                            assert(post.cache[addr] == pre.cache[addr]);
                            assert(post.visible()[addr] == pre.visible()[addr]);
                        } else if post.persistent.contains_key(addr) {
                            assert(!pre.cache.contains_key(addr)) by {
                                if pre.cache.contains_key(addr) {
                                    assert(post.cache.contains_key(addr));
                                    assert(false);
                                }
                            }
                            assert(pre.persistent.contains_key(addr)) by {
                                if !pre.persistent.contains_key(addr) {
                                    assert((post.persistent.dom() - pre.persistent.dom()).contains(addr));
                                    assert(false);
                                }
                            }
                            assert(post.visible()[addr] == pre.visible()[addr]);
                        }
                        if pre.cache.contains_key(addr) {
                            assert(post.cache.contains_key(addr));
                            assert(post.cache[addr] == pre.cache[addr]);
                            assert(post.visible()[addr] == pre.visible()[addr]);
                        } else if pre.persistent.contains_key(addr) {
                            assert(post.persistent.contains_key(addr));
                            assert(!post.cache.contains_key(addr)) by {
                                if post.cache.contains_key(addr) {
                                    assert(!pre.cache.contains_key(addr));
                                    assert((post.cache.dom() - pre.cache.dom()).contains(addr));
                                    assert(false);
                                }
                            }
                            assert(post.visible()[addr] == pre.visible()[addr]);
                        }
                    }
                }
            );
        }
        Self::same_views_preserve_persistent_visible_agree_on(pre, post, addrs);
    }

    pub proof fn access_preserves_persistent_visible_agree_on(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addrs: Set<Address>,
    )
        requires
            pre.persistent_visible_agree_on(addrs),
            writes.dom().disjoint(addrs),
            CachingDisk::State::next(
                pre,
                post,
                CachingDisk::Label::Access{reads, writes},
            ),
        ensures
            post.persistent_visible_agree_on(addrs),
    {
        Self::access_visible_effect(pre, post, reads, writes);
        assert(post.persistent == pre.persistent) by {
            Self::access_effect(pre, post, reads, writes);
        }
        assert_maps_equal!(
            post.persistent.restrict(addrs),
            post.visible().restrict(addrs),
            addr => {
                if addrs.contains(addr) {
                    assert(!writes.contains_key(addr)) by {
                        if writes.contains_key(addr) {
                            assert(writes.dom().contains(addr));
                            assert(writes.dom().disjoint(addrs));
                            assert(false);
                        }
                    }
                    assert(post.visible() == pre.visible().union_prefer_right(writes));
                    if post.persistent.contains_key(addr) {
                        assert(pre.persistent.contains_key(addr));
                        assert(post.persistent[addr] == pre.persistent[addr]);
                        assert(pre.persistent.restrict(addrs)
                            == pre.visible().restrict(addrs));
                        assert(pre.persistent.restrict(addrs).contains_key(addr));
                        assert(pre.visible().restrict(addrs).contains_key(addr));
                        assert(pre.persistent.restrict(addrs)[addr]
                            == pre.visible().restrict(addrs)[addr]);
                        assert(pre.persistent.restrict(addrs)[addr]
                            == pre.persistent[addr]);
                        assert(pre.visible().restrict(addrs)[addr]
                            == pre.visible()[addr]);
                        assert(pre.persistent[addr] == pre.visible()[addr]);
                    }
                    if post.visible().contains_key(addr) {
                        assert(pre.visible().contains_key(addr));
                        assert(pre.persistent.restrict(addrs)
                            == pre.visible().restrict(addrs));
                        assert(pre.visible().restrict(addrs).contains_key(addr));
                        assert(pre.persistent.restrict(addrs).contains_key(addr));
                        assert(pre.persistent.contains_key(addr));
                        assert(post.persistent.contains_key(addr));
                    }
                }
            }
        );
    }

    pub proof fn forget_preserves_persistent_visible_agree_on(
        pre: Self,
        post: Self,
        aus: Set<AU>,
        addrs: Set<Address>,
    )
        requires
            pre.persistent_visible_agree_on(addrs),
            addresses_in_aus(aus).disjoint(addrs),
            CachingDisk::State::next(
                pre,
                post,
                CachingDisk::Label::Forget{aus},
            ),
        ensures
            post.persistent_visible_agree_on(addrs),
    {
        Self::forget_effect(pre, post, aus);
        assert(post.persistent.restrict(addrs) == pre.persistent.restrict(addrs)) by {
            assert_maps_equal!(
                post.persistent.restrict(addrs),
                pre.persistent.restrict(addrs),
                addr => {
                    if addrs.contains(addr) {
                        assert(!addresses_in_aus(aus).contains(addr));
                    }
                }
            );
        }
        assert(post.visible().restrict(addrs) == pre.visible().restrict(addrs)) by {
            assert_maps_equal!(
                post.visible().restrict(addrs),
                pre.visible().restrict(addrs),
                addr => {
                    if addrs.contains(addr) {
                        assert(!addresses_in_aus(aus).contains(addr));
                    }
                }
            );
        }
        Self::same_views_preserve_persistent_visible_agree_on(pre, post, addrs);
    }

    pub proof fn internal_preserves_aus_clean_or_evictable(pre: Self, post: Self, aus: Set<AU>)
        requires
            pre.inv(),
            post.inv(),
            pre.aus_clean_or_evictable(aus),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Internal{}),
        ensures
            post.aus_clean_or_evictable(aus),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::load(addrs) => {
                Self::load_effect(pre, post, addrs);
            },
            CachingDisk::Step::begin_writeback(addrs) => {
                Self::begin_writeback_effect(pre, post, addrs);
            },
            CachingDisk::Step::persist_writeback(addrs) => {
                Self::persist_writeback_effect(pre, post, addrs);
            },
            CachingDisk::Step::mark_clean(addrs_to_clean) => {
                Self::mark_clean_effect(pre, post, addrs_to_clean);
            },
            CachingDisk::Step::evict_clean(addrs) => {
                Self::evict_clean_effect(pre, post, addrs);
            },
            CachingDisk::Step::internal_noop() => {
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }

        assert forall |addr: Address| #[trigger] post.cache.contains_key(addr) && aus.contains(addr.au)
            implies {
                &&& post.status.contains_key(addr)
                &&& post.status[addr] == PageStatus::Clean
            }
        by {
            match step {
                CachingDisk::Step::load(addrs) => {
                    if addrs.contains(addr) {
                    } else {
                        assert(pre.cache.contains_key(addr));
                        assert(pre.aus_clean_or_evictable(aus));
                    }
                },
                CachingDisk::Step::begin_writeback(addrs) => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.aus_clean_or_evictable(aus));
                    if addrs.contains(addr) {
                        assert(pre.all_status(addrs, PageStatus::Dirty));
                        assert(pre.status[addr] == PageStatus::Dirty);
                        assert(pre.status[addr] == PageStatus::Clean);
                        assert(false);
                    }
                },
                CachingDisk::Step::persist_writeback(addrs) => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.aus_clean_or_evictable(aus));
                },
                CachingDisk::Step::mark_clean(addrs_to_clean) => {
                    if addrs_to_clean.contains(addr) {
                    } else {
                        assert(pre.cache.contains_key(addr));
                        assert(pre.aus_clean_or_evictable(aus));
                    }
                },
                CachingDisk::Step::evict_clean(addrs) => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.aus_clean_or_evictable(aus));
                },
                CachingDisk::Step::internal_noop() => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.aus_clean_or_evictable(aus));
                },
                _ => {
                    assert(false);
                },
            }
        };
    }

    pub proof fn access_preserves_aus_clean_or_evictable(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        aus: Set<AU>,
    )
        requires
            pre.inv(),
            post.inv(),
            pre.aus_clean_or_evictable(aus),
            writes.dom().disjoint(addresses_in_aus(aus)),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Access{reads, writes}),
        ensures
            post.aus_clean_or_evictable(aus),
    {
        Self::access_effect(pre, post, reads, writes);
        assert forall |addr: Address| #[trigger] post.cache.contains_key(addr) && aus.contains(addr.au)
            implies {
                &&& post.status.contains_key(addr)
                &&& post.status[addr] == PageStatus::Clean
            }
        by {
            if writes.contains_key(addr) {
                assert(writes.dom().contains(addr));
                assert(addresses_in_aus(aus).contains(addr));
                assert(false);
            } else {
                assert(pre.cache.contains_key(addr));
                assert(pre.aus_clean_or_evictable(aus));
            }
        };
    }

    pub proof fn internal_preserves_addrs_clean_or_evictable(pre: Self, post: Self, addrs: Set<Address>)
        requires
            pre.inv(),
            post.inv(),
            pre.addrs_clean_or_evictable(addrs),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Internal{}),
        ensures
            post.addrs_clean_or_evictable(addrs),
    {
        reveal(CachingDisk::State::next);
        reveal(CachingDisk::State::next_by);
        let lbl = CachingDisk::Label::Internal{};
        let step = choose |step| CachingDisk::State::next_by(pre, post, lbl, step);
        match step {
            CachingDisk::Step::load(addrs_to_load) => {
                Self::load_effect(pre, post, addrs_to_load);
            },
            CachingDisk::Step::begin_writeback(addrs_to_writeback) => {
                Self::begin_writeback_effect(pre, post, addrs_to_writeback);
            },
            CachingDisk::Step::persist_writeback(addrs_to_persist) => {
                Self::persist_writeback_effect(pre, post, addrs_to_persist);
            },
            CachingDisk::Step::mark_clean(addrs_to_clean) => {
                Self::mark_clean_effect(pre, post, addrs_to_clean);
            },
            CachingDisk::Step::evict_clean(addrs_to_evict) => {
                Self::evict_clean_effect(pre, post, addrs_to_evict);
            },
            CachingDisk::Step::internal_noop() => {
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }

        assert forall |addr: Address| #[trigger] post.cache.contains_key(addr) && addrs.contains(addr)
            implies {
                &&& post.status.contains_key(addr)
                &&& post.status[addr] == PageStatus::Clean
            }
        by {
            match step {
                CachingDisk::Step::load(addrs_to_load) => {
                    if addrs_to_load.contains(addr) {
                    } else {
                        assert(pre.cache.contains_key(addr));
                        assert(pre.addrs_clean_or_evictable(addrs));
                    }
                },
                CachingDisk::Step::begin_writeback(addrs_to_writeback) => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.addrs_clean_or_evictable(addrs));
                    if addrs_to_writeback.contains(addr) {
                        assert(pre.all_status(addrs_to_writeback, PageStatus::Dirty));
                        assert(pre.status[addr] == PageStatus::Dirty);
                        assert(pre.status[addr] == PageStatus::Clean);
                        assert(false);
                    }
                },
                CachingDisk::Step::persist_writeback(addrs_to_persist) => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.addrs_clean_or_evictable(addrs));
                },
                CachingDisk::Step::mark_clean(addrs_to_clean) => {
                    if addrs_to_clean.contains(addr) {
                    } else {
                        assert(pre.cache.contains_key(addr));
                        assert(pre.addrs_clean_or_evictable(addrs));
                    }
                },
                CachingDisk::Step::evict_clean(addrs_to_evict) => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.addrs_clean_or_evictable(addrs));
                },
                CachingDisk::Step::internal_noop() => {
                    assert(pre.cache.contains_key(addr));
                    assert(pre.addrs_clean_or_evictable(addrs));
                },
                _ => {
                    assert(false);
                },
            }
        };
    }

    pub proof fn access_preserves_addrs_clean_or_evictable(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addrs: Set<Address>,
    )
        requires
            pre.inv(),
            post.inv(),
            pre.addrs_clean_or_evictable(addrs),
            writes.dom().disjoint(addrs),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Access{reads, writes}),
        ensures
            post.addrs_clean_or_evictable(addrs),
    {
        Self::access_effect(pre, post, reads, writes);
        assert forall |addr: Address| #[trigger] post.cache.contains_key(addr) && addrs.contains(addr)
            implies {
                &&& post.status.contains_key(addr)
                &&& post.status[addr] == PageStatus::Clean
            }
        by {
            if writes.contains_key(addr) {
                assert(writes.dom().contains(addr));
                assert(false);
            } else {
                assert(pre.cache.contains_key(addr));
                assert(pre.addrs_clean_or_evictable(addrs));
            }
        };
    }

    pub proof fn forget_preserves_addrs_clean_or_evictable(
        pre: Self,
        post: Self,
        aus: Set<AU>,
        addrs: Set<Address>,
    )
        requires
            pre.addrs_clean_or_evictable(addrs),
            CachingDisk::State::next(pre, post, CachingDisk::Label::Forget{aus}),
        ensures
            post.addrs_clean_or_evictable(addrs),
    {
        Self::forget_effect(pre, post, aus);
        assert forall |addr: Address| #[trigger] post.cache.contains_key(addr) && addrs.contains(addr)
            implies {
                &&& post.status.contains_key(addr)
                &&& post.status[addr] == PageStatus::Clean
            }
        by {
            assert(pre.cache.contains_key(addr));
            assert(pre.addrs_clean_or_evictable(addrs));
        };
    }
}

} // verus!
