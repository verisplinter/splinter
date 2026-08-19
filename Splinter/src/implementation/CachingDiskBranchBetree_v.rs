// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// CachedBranchBetree backed by a caching disk with operation-local page decoding.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::Likes_v::AULikes;
use crate::betree::Buffer_v::Buffer;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBetree_v::{
    BetreeNode, PathAddrs, SplitAddrs, TwoAddrs,
};
use crate::betree::LinkedBranch_v::{LinkedBranch, SplitArg};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::CachedBranch_v::{LoadedPathReceipt};
use crate::implementation::BranchProofUtils_v::tight_branch_in_loose_disk;
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree, CachedBranchBetreeAccess, FrozenBranchBetree,
    LoadedBetree, LoadedBetreePath, LoadedBetreeQueryReceipt,
};
use crate::implementation::CachedBulkBranch_v::{
    CachedBulkBranch, CachedBulkBranchEvent,
};
use crate::implementation::CachingDisk_v::{
    CachingDisk, PageStatus, addresses_in_aus, status_map,
};
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::marshalling::IBetreeNodeFormat_v::raw_page_to_betree_node;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};

verus! {

pub open spec fn to_betree_nodes(
    raw_pages: Map<Address, RawPage>,
) -> LoadedBetree {
    Map::new(
        |addr: Address| raw_pages.contains_key(addr),
        |addr: Address| raw_page_to_betree_node(raw_pages[addr]),
    )
}

pub open spec fn to_branch_nodes(
    raw_pages: Map<Address, RawPage>,
) -> crate::implementation::CachedBranch_v::LoadedBranch {
    Map::new(
        |addr: Address| raw_pages.contains_key(addr),
        |addr: Address| raw_page_to_branch_node(raw_pages[addr]),
    )
}

pub open spec fn visible_branch_disk(
    disk: CachingDisk::State,
    branch_summary: Map<AU, Summary>,
) -> BufferDisk<BranchNode> {
    BufferDisk {
        entries: to_branch_nodes(disk.visible()).restrict(
            addresses_in_aus(summary_aus(branch_summary)),
        ),
    }
}

pub open spec fn loose_disk_for_summary(
    loose_disk: BufferDisk<BranchNode>,
    summary: Summary,
) -> BufferDisk<BranchNode> {
    BufferDisk {
        entries: loose_disk.entries.restrict(addresses_in_aus(summary)),
    }
}

pub open spec fn tight_branch_exists(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
) -> bool {
    exists |branch: LinkedBranch<Summary>| #[trigger] tight_branch_in_loose_disk(
        loose_disk,
        root,
        summary,
        branch,
    )
}

pub open spec fn tight_branch_of(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
) -> LinkedBranch<Summary> {
    choose |branch: LinkedBranch<Summary>| tight_branch_in_loose_disk(
        loose_disk,
        root,
        summary,
        branch,
    )
}

pub open spec fn tight_branch_addrs(
    loose_disk: BufferDisk<BranchNode>,
    roots: Set<Address>,
    branch_summary: Map<AU, Summary>,
) -> Set<Address> {
    Set::new(|addr: Address| exists |root: Address|
        roots.contains(root)
        && tight_branch_of(
            loose_disk_for_summary(loose_disk, branch_summary[root.au]),
            root,
            branch_summary[root.au],
        ).disk_view.entries.contains_key(addr))
}

pub open spec fn tight_sealed_branch_disk(
    loose_disk: BufferDisk<BranchNode>,
    roots: Set<Address>,
    branch_summary: Map<AU, Summary>,
) -> BufferDisk<BranchNode> {
    BufferDisk {
        entries: loose_disk.entries.restrict(
            tight_branch_addrs(loose_disk, roots, branch_summary),
        ),
    }
}

pub open spec fn disk_namespace(disk: CachingDisk::State) -> Set<Address> {
    disk.cache.dom() + disk.persistent.dom()
}

pub open spec fn disk_extend_for_alloc(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
) -> bool {
    &&& post.inv()
    &&& pre.cache <= post.cache
    &&& pre.persistent <= post.persistent
    &&& pre.status <= post.status
    &&& disk_namespace(post) - disk_namespace(pre) <= addresses_in_aus(allocs)
    &&& post.cache.dom() - pre.cache.dom() <= addresses_in_aus(allocs)
    &&& post.persistent.dom() - pre.persistent.dom() <= addresses_in_aus(allocs)
}

pub proof fn disk_extend_empty_is_identity(
    pre: CachingDisk::State,
    post: CachingDisk::State,
)
    requires
        pre.inv(),
        disk_extend_for_alloc(pre, post, Set::empty()),
    ensures post == pre
{
    assert forall |addr: Address| #[trigger] post.cache.contains_key(addr)
        <==> pre.cache.contains_key(addr) by {
        if post.cache.contains_key(addr) && !pre.cache.contains_key(addr) {
            assert((post.cache.dom() - pre.cache.dom()).contains(addr));
            assert(addresses_in_aus(Set::empty()).contains(addr));
            assert(false);
        }
    };
    assert forall |addr: Address| #[trigger] post.persistent.contains_key(addr)
        <==> pre.persistent.contains_key(addr) by {
        if post.persistent.contains_key(addr) && !pre.persistent.contains_key(addr) {
            assert((post.persistent.dom() - pre.persistent.dom()).contains(addr));
            assert(addresses_in_aus(Set::empty()).contains(addr));
            assert(false);
        }
    };
    assert(post.cache.dom() == pre.cache.dom());
    assert(post.persistent.dom() == pre.persistent.dom());
    assert_maps_equal!(post.cache, pre.cache, addr => {});
    assert_maps_equal!(post.persistent, pre.persistent, addr => {});
    assert(post.status.dom() == post.cache.dom());
    assert(pre.status.dom() == pre.cache.dom());
    assert_maps_equal!(post.status, pre.status, addr => {});
}

pub struct DiskAccessWitness {
    pub expanded: CachingDisk::State,
    pub accessed: CachingDisk::State,
}

pub open spec fn disk_access_for_alloc(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
) -> bool {
    exists |witness: DiskAccessWitness| {
        &&& #[trigger] disk_extend_for_alloc(pre, witness.expanded, allocs)
        &&& CachingDisk::State::next(
            witness.expanded,
            witness.accessed,
            CachingDisk::Label::Access{reads, writes},
        )
        &&& CachingDisk::State::next(
            witness.accessed,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        )
    }
}

pub proof fn disk_access_for_alloc_preserves_inv(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires disk_access_for_alloc(
        pre, post, allocs, deallocs, guard_aus, reads, writes,
    )
    ensures post.inv()
{
    let witness = choose |witness: DiskAccessWitness| {
        &&& #[trigger] disk_extend_for_alloc(pre, witness.expanded, allocs)
        &&& CachingDisk::State::next(
            witness.expanded,
            witness.accessed,
            CachingDisk::Label::Access{reads, writes},
        )
        &&& CachingDisk::State::next(
            witness.accessed,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        )
    };
    CachingDisk::State::inv_next(
        witness.expanded,
        witness.accessed,
        CachingDisk::Label::Access{reads, writes},
    );
    CachingDisk::State::inv_next(
        witness.accessed,
        post,
        CachingDisk::Label::Forget{aus: deallocs - guard_aus},
    );
}

pub proof fn disk_access_for_alloc_witness(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
) -> (witness: DiskAccessWitness)
    requires disk_access_for_alloc(
        pre, post, allocs, deallocs, guard_aus, reads, writes,
    )
    ensures
        disk_extend_for_alloc(pre, witness.expanded, allocs),
        CachingDisk::State::next(
            witness.expanded,
            witness.accessed,
            CachingDisk::Label::Access{reads, writes},
        ),
        CachingDisk::State::next(
            witness.accessed,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        ),
        reads <= witness.expanded.cache,
        witness.accessed.visible()
            == witness.expanded.visible().union_prefer_right(writes),
        post.visible() == witness.accessed.visible().remove_keys(
            addresses_in_aus(deallocs - guard_aus),
        ),
{
    let witness = choose |witness: DiskAccessWitness| {
        &&& #[trigger] disk_extend_for_alloc(pre, witness.expanded, allocs)
        &&& CachingDisk::State::next(
            witness.expanded,
            witness.accessed,
            CachingDisk::Label::Access{reads, writes},
        )
        &&& CachingDisk::State::next(
            witness.accessed,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        )
    };
    CachingDisk::State::access_visible_effect(
        witness.expanded,
        witness.accessed,
        reads,
        writes,
    );
    CachingDisk::State::forget_effect(
        witness.accessed,
        post,
        deallocs - guard_aus,
    );
    witness
}

pub proof fn disk_access_for_alloc_visible_outside_alloc_dealloc(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    stable_addrs: Set<Address>,
)
    requires
        pre.inv(),
        disk_access_for_alloc(
            pre, post, allocs, deallocs, guard_aus, reads, writes,
        ),
        writes.dom() <= addresses_in_aus(allocs),
        stable_addrs.disjoint(addresses_in_aus(allocs)),
        stable_addrs.disjoint(addresses_in_aus(deallocs - guard_aus)),
    ensures
        post.visible().restrict(stable_addrs)
            == pre.visible().restrict(stable_addrs),
{
    let witness = disk_access_for_alloc_witness(
        pre, post, allocs, deallocs, guard_aus, reads, writes,
    );
    disk_extend_visible_outside_allocs(
        pre,
        witness.expanded,
        allocs,
        stable_addrs,
    );
    assert_maps_equal!(
        post.visible().restrict(stable_addrs),
        pre.visible().restrict(stable_addrs),
        addr => {
            if stable_addrs.contains(addr) {
                assert(!addresses_in_aus(allocs).contains(addr));
                assert(!writes.contains_key(addr));
                assert(!addresses_in_aus(
                    deallocs - guard_aus,
                ).contains(addr));
                assert(witness.accessed.visible()
                    == witness.expanded.visible().union_prefer_right(writes));
                if pre.visible().contains_key(addr) {
                    assert(pre.visible().restrict(stable_addrs).contains_key(addr));
                    assert(witness.expanded.visible().restrict(stable_addrs)
                        .contains_key(addr));
                    assert(witness.expanded.visible().contains_key(addr));
                    assert(witness.expanded.visible().union_prefer_right(writes)[addr]
                        == witness.expanded.visible()[addr]);
                    assert(witness.accessed.visible()[addr]
                        == witness.expanded.visible()[addr]);
                }
                if post.visible().contains_key(addr) {
                    assert(post.visible()
                        == witness.accessed.visible().remove_keys(
                            addresses_in_aus(deallocs - guard_aus),
                        ));
                    assert(witness.accessed.visible().contains_key(addr));
                    assert(witness.expanded.visible().contains_key(addr));
                    assert(witness.expanded.visible().union_prefer_right(writes)[addr]
                        == witness.expanded.visible()[addr]);
                    assert(witness.accessed.visible()[addr]
                        == witness.expanded.visible()[addr]);
                }
            }
        }
    );
}

pub proof fn disk_access_for_alloc_visible_on_stable(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    stable_addrs: Set<Address>,
)
    requires
        pre.inv(),
        disk_access_for_alloc(
            pre, post, allocs, deallocs, guard_aus, reads, writes,
        ),
        stable_addrs.disjoint(addresses_in_aus(allocs)),
        stable_addrs.disjoint(addresses_in_aus(deallocs - guard_aus)),
        stable_addrs.disjoint(writes.dom()),
    ensures
        post.visible().restrict(stable_addrs)
            == pre.visible().restrict(stable_addrs),
{
    let witness = disk_access_for_alloc_witness(
        pre, post, allocs, deallocs, guard_aus, reads, writes,
    );
    disk_extend_visible_outside_allocs(
        pre, witness.expanded, allocs, stable_addrs,
    );
    assert_maps_equal!(
        post.visible().restrict(stable_addrs),
        pre.visible().restrict(stable_addrs),
        addr => {
            if stable_addrs.contains(addr) {
                assert(!writes.contains_key(addr));
                assert(!addresses_in_aus(
                    deallocs - guard_aus,
                ).contains(addr));
            }
        }
    );
}

pub proof fn disk_access_empty_effect_is_extension(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    guard_aus: Set<AU>,
)
    requires disk_access_for_alloc(
        pre,
        post,
        allocs,
        Set::empty(),
        guard_aus,
        Map::empty(),
        Map::empty(),
    ),
    ensures disk_extend_for_alloc(pre, post, allocs),
{
    let witness = disk_access_for_alloc_witness(
        pre,
        post,
        allocs,
        Set::empty(),
        guard_aus,
        Map::empty(),
        Map::empty(),
    );
    CachingDisk::State::access_effect(
        witness.expanded,
        witness.accessed,
        Map::empty(),
        Map::empty(),
    );
    assert(Set::<AU>::empty() - guard_aus == Set::<AU>::empty());
    CachingDisk::State::forget_effect(
        witness.accessed,
        post,
        Set::empty(),
    );
    assert(witness.accessed == witness.expanded);
    assert(post == witness.accessed);
}

pub proof fn disk_access_empty_alloc_access_is_forget(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
)
    requires
        pre.inv(),
        disk_access_for_alloc(
            pre,
            post,
            Set::empty(),
            deallocs,
            guard_aus,
            Map::empty(),
            Map::empty(),
        ),
    ensures CachingDisk::State::next(
        pre,
        post,
        CachingDisk::Label::Forget{aus: deallocs - guard_aus},
    ),
{
    let witness = disk_access_for_alloc_witness(
        pre,
        post,
        Set::empty(),
        deallocs,
        guard_aus,
        Map::empty(),
        Map::empty(),
    );
    disk_extend_empty_is_identity(pre, witness.expanded);
    CachingDisk::State::access_effect(
        witness.expanded,
        witness.accessed,
        Map::empty(),
        Map::empty(),
    );
    assert(witness.accessed == witness.expanded);
}

pub proof fn disk_extension_is_empty_alloc_access(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    guard_aus: Set<AU>,
)
    requires
        pre.inv(),
        disk_extend_for_alloc(pre, post, allocs),
    ensures disk_access_for_alloc(
        pre,
        post,
        allocs,
        Set::empty(),
        guard_aus,
        Map::empty(),
        Map::empty(),
    ),
{
    let empty_access = CachingDisk::Label::Access {
        reads: Map::empty(),
        writes: Map::empty(),
    };
    assert(CachingDisk::State::access(post, post, empty_access)) by {
        assert(post.cache.union_prefer_right(Map::empty()) == post.cache);
        assert(status_map(Map::<Address, RawPage>::empty().dom(), PageStatus::Dirty)
            .is_empty());
        assert(post.status.union_prefer_right(
            status_map(Map::<Address, RawPage>::empty().dom(), PageStatus::Dirty),
        ) == post.status);
    }
    assert(CachingDisk::State::next_by(
        post,
        post,
        empty_access,
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    let empty_forget = CachingDisk::Label::Forget {
        aus: Set::<AU>::empty() - guard_aus,
    };
    assert(Set::<AU>::empty() - guard_aus == Set::<AU>::empty());
    assert(CachingDisk::State::forget(post, post, empty_forget)) by {
        assert(addresses_in_aus(Set::<AU>::empty()).is_empty());
        assert(post.cache.remove_keys(Set::<Address>::empty()) == post.cache);
        assert(post.persistent.remove_keys(Set::<Address>::empty()) == post.persistent);
        assert(post.status.remove_keys(Set::<Address>::empty()) == post.status);
    }
    assert(CachingDisk::State::next_by(
        post,
        post,
        empty_forget,
        CachingDisk::Step::forget(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    let witness = DiskAccessWitness { expanded: post, accessed: post };
    assert(disk_extend_for_alloc(pre, witness.expanded, allocs));
    assert(CachingDisk::State::next(
        witness.expanded,
        witness.accessed,
        empty_access,
    ));
    assert(CachingDisk::State::next(
        witness.accessed,
        post,
        empty_forget,
    ));
}

pub proof fn disk_forget_is_empty_alloc_access(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
)
    requires
        pre.inv(),
        CachingDisk::State::next(
            pre,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        ),
    ensures disk_access_for_alloc(
        pre,
        post,
        Set::empty(),
        deallocs,
        guard_aus,
        Map::empty(),
        Map::empty(),
    ),
{
    assert(disk_extend_for_alloc(pre, pre, Set::empty()));
    let empty_access = CachingDisk::Label::Access {
        reads: Map::empty(),
        writes: Map::empty(),
    };
    assert(CachingDisk::State::access(pre, pre, empty_access)) by {
        assert(pre.cache.union_prefer_right(Map::empty()) == pre.cache);
        assert(status_map(Map::<Address, RawPage>::empty().dom(), PageStatus::Dirty)
            .is_empty());
        assert(pre.status.union_prefer_right(
            status_map(Map::<Address, RawPage>::empty().dom(), PageStatus::Dirty),
        ) == pre.status);
    }
    assert(CachingDisk::State::next_by(
        pre,
        pre,
        empty_access,
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    let witness = DiskAccessWitness { expanded: pre, accessed: pre };
    assert(CachingDisk::State::next(
        witness.accessed,
        post,
        CachingDisk::Label::Forget{aus: deallocs - guard_aus},
    ));
    assert(exists |witness: DiskAccessWitness| {
        &&& #[trigger] disk_extend_for_alloc(pre, witness.expanded, Set::empty())
        &&& CachingDisk::State::next(
            witness.expanded,
            witness.accessed,
            empty_access,
        )
        &&& CachingDisk::State::next(
            witness.accessed,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        )
    }) by {
        let witness = DiskAccessWitness { expanded: pre, accessed: pre };
        assert(disk_extend_for_alloc(
            pre, witness.expanded, Set::empty(),
        ));
        assert(CachingDisk::State::next(
            witness.expanded, witness.accessed, empty_access,
        ));
        assert(CachingDisk::State::next(
            witness.accessed,
            post,
            CachingDisk::Label::Forget{aus: deallocs - guard_aus},
        ));
    }
}

pub proof fn disk_access_empty_alloc_visible_stable(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    stable_addrs: Set<Address>,
)
    requires
        pre.inv(),
        disk_access_for_alloc(
            pre,
            post,
            Set::empty(),
            deallocs,
            guard_aus,
            reads,
            writes,
        ),
        stable_addrs.disjoint(writes.dom()),
        stable_addrs.disjoint(addresses_in_aus(deallocs - guard_aus)),
    ensures
        post.visible().restrict(stable_addrs)
            == pre.visible().restrict(stable_addrs),
{
    let witness = disk_access_for_alloc_witness(
        pre,
        post,
        Set::empty(),
        deallocs,
        guard_aus,
        reads,
        writes,
    );
    disk_extend_empty_is_identity(pre, witness.expanded);
    assert_maps_equal!(
        post.visible().restrict(stable_addrs),
        pre.visible().restrict(stable_addrs),
        addr => {
            if stable_addrs.contains(addr) {
                assert(!writes.contains_key(addr));
                assert(!addresses_in_aus(
                    deallocs - guard_aus,
                ).contains(addr));
            }
        }
    );
}

pub open spec fn reclaim_guarded_aus(
    pre: CachingDiskBranchBetree::State,
    post: CachingDiskBranchBetree::State,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
) -> bool {
    &&& post.betree == pre.betree
    &&& CachingDisk::State::next(
        pre.disk,
        post.disk,
        CachingDisk::Label::Forget{
            aus: deallocs - guard_aus,
        },
    )
}

pub proof fn reclaim_guarded_aus_preserves_inv(
    pre: CachingDiskBranchBetree::State,
    post: CachingDiskBranchBetree::State,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
)
    requires
        pre.inv(),
        reclaim_guarded_aus(pre, post, deallocs, guard_aus),
    ensures post.inv(),
{
    CachingDisk::State::inv_next(
        pre.disk,
        post.disk,
        CachingDisk::Label::Forget{
            aus: deallocs - guard_aus,
        },
    );
}

pub proof fn disk_extend_visible_outside_allocs(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    allocs: Set<AU>,
    addrs: Set<Address>,
)
    requires
        pre.inv(),
        disk_extend_for_alloc(pre, post, allocs),
        addresses_in_aus(allocs).disjoint(addrs),
    ensures
        post.visible().restrict(addrs) == pre.visible().restrict(addrs),
{
    assert_maps_equal!(
        post.visible().restrict(addrs),
        pre.visible().restrict(addrs),
        addr => {
            if addrs.contains(addr) {
                assert(!addresses_in_aus(allocs).contains(addr));
                assert(post.cache.contains_key(addr) == pre.cache.contains_key(addr)) by {
                    if post.cache.contains_key(addr) && !pre.cache.contains_key(addr) {
                        assert((post.cache.dom() - pre.cache.dom()).contains(addr));
                    }
                }
                assert(post.persistent.contains_key(addr)
                    == pre.persistent.contains_key(addr)) by {
                    if post.persistent.contains_key(addr)
                        && !pre.persistent.contains_key(addr)
                    {
                        assert((post.persistent.dom() - pre.persistent.dom()).contains(addr));
                    }
                }
                if pre.cache.contains_key(addr) {
                    assert(pre.status.contains_key(addr));
                    assert(post.status.contains_key(addr));
                    assert(post.cache[addr] == pre.cache[addr]);
                    assert(post.status[addr] == pre.status[addr]);
                }
                if pre.persistent.contains_key(addr) {
                    assert(post.persistent[addr] == pre.persistent[addr]);
                }
            }
        }
    );
}

pub proof fn disk_forget_visible_outside_aus(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    aus: Set<AU>,
    addrs: Set<Address>,
)
    requires
        CachingDisk::State::next(
            pre,
            post,
            CachingDisk::Label::Forget{aus},
        ),
        addresses_in_aus(aus).disjoint(addrs),
    ensures
        post.visible().restrict(addrs) == pre.visible().restrict(addrs),
{
    CachingDisk::State::forget_effect(pre, post, aus);
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

pub struct PageAccess {
    pub betree_reads: Map<Address, RawPage>,
    pub branch_reads: Map<Address, RawPage>,
    pub betree_writes: Map<Address, RawPage>,
    pub branch_writes: Map<Address, RawPage>,
}

impl PageAccess {
    pub open spec fn empty() -> Self {
        PageAccess {
            betree_reads: Map::empty(),
            branch_reads: Map::empty(),
            betree_writes: Map::empty(),
            branch_writes: Map::empty(),
        }
    }

    pub open spec fn reads(self) -> Map<Address, RawPage> {
        self.betree_reads.union_prefer_right(self.branch_reads)
    }

    pub open spec fn writes(self) -> Map<Address, RawPage> {
        self.betree_writes.union_prefer_right(self.branch_writes)
    }

    pub open spec fn loaded_betree_reads(self) -> LoadedBetree {
        to_betree_nodes(self.betree_reads)
    }

    pub open spec fn loaded_betree_writes(self) -> LoadedBetree {
        to_betree_nodes(self.betree_writes)
    }

    pub open spec fn loaded_branch_reads(
        self,
    ) -> crate::implementation::CachedBranch_v::LoadedBranch {
        to_branch_nodes(self.branch_reads)
    }

    pub open spec fn loaded_branch_writes(
        self,
    ) -> crate::implementation::CachedBranch_v::LoadedBranch {
        to_branch_nodes(self.branch_writes)
    }

    pub open spec fn cached_access(self) -> CachedBranchBetreeAccess {
        CachedBranchBetreeAccess {
            betree_reads: self.loaded_betree_reads(),
            branch_reads: self.loaded_branch_reads(),
            betree_writes: self.loaded_betree_writes(),
            branch_writes: self.loaded_branch_writes(),
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& self.betree_reads.dom().disjoint(self.branch_reads.dom())
        &&& self.betree_writes.dom().disjoint(self.branch_writes.dom())
    }

    pub open spec fn read_only(self) -> bool {
        self.betree_writes.is_empty() && self.branch_writes.is_empty()
    }

    pub open spec fn only_betree(self) -> bool {
        self.branch_reads.is_empty() && self.branch_writes.is_empty()
    }

    pub open spec fn only_branch(self) -> bool {
        self.betree_reads.is_empty() && self.betree_writes.is_empty()
    }

    pub proof fn typed_read_domains_disjoint(self)
        requires self.wf()
        ensures self.loaded_betree_reads().dom().disjoint(
            self.loaded_branch_reads().dom(),
        )
    {
    }

    pub proof fn typed_write_domains_disjoint(self)
        requires self.wf()
        ensures self.loaded_betree_writes().dom().disjoint(
            self.loaded_branch_writes().dom(),
        )
    {
    }

    pub proof fn cached_empty_is_empty(self)
        requires self.cached_access() == CachedBranchBetreeAccess::empty(),
        ensures self == Self::empty(),
    {
        assert(self.betree_reads.dom()
            == self.loaded_betree_reads().dom());
        assert(self.branch_reads.dom()
            == self.loaded_branch_reads().dom());
        assert(self.betree_writes.dom()
            == self.loaded_betree_writes().dom());
        assert(self.branch_writes.dom()
            == self.loaded_branch_writes().dom());
        assert(self.betree_reads.is_empty());
        assert(self.branch_reads.is_empty());
        assert(self.betree_writes.is_empty());
        assert(self.branch_writes.is_empty());
        assert_maps_equal!(self.betree_reads, Map::empty(), addr => {});
        assert_maps_equal!(self.branch_reads, Map::empty(), addr => {});
        assert_maps_equal!(self.betree_writes, Map::empty(), addr => {});
        assert_maps_equal!(self.branch_writes, Map::empty(), addr => {});
    }

    pub proof fn empty_cached_access_is_empty()
        ensures Self::empty().cached_access() == CachedBranchBetreeAccess::empty(),
    {
        assert_maps_equal!(
            to_betree_nodes(Map::empty()), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            to_branch_nodes(Map::empty()), Map::empty(), addr => {}
        );
    }

    pub proof fn empty_effects_are_empty()
        ensures
            Self::empty().reads() == Map::<Address, RawPage>::empty(),
            Self::empty().writes() == Map::<Address, RawPage>::empty(),
    {
        assert_maps_equal!(
            Self::empty().reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            Self::empty().writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_betree_read_only_shape(self)
        requires
            self.only_betree(),
            self.read_only(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            betree_reads: self.loaded_betree_reads(),
            ..CachedBranchBetreeAccess::empty()
        }),
    {
        assert_maps_equal!(
            self.loaded_branch_reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_betree_writes(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_branch_writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_branch_read_only_shape(self)
        requires
            self.only_branch(),
            self.read_only(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            branch_reads: self.loaded_branch_reads(),
            ..CachedBranchBetreeAccess::empty()
        }),
    {
        assert_maps_equal!(
            self.loaded_betree_reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_betree_writes(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_branch_writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_write_only_betree_shape(self)
        requires
            self.betree_reads.is_empty(),
            self.branch_reads.is_empty(),
            self.branch_writes.is_empty(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            betree_writes: self.loaded_betree_writes(),
            ..CachedBranchBetreeAccess::empty()
        }),
    {
        assert_maps_equal!(
            self.loaded_betree_reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_branch_reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_branch_writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_only_betree_is_only_betree(self)
        requires
            self.cached_access().branch_reads.is_empty(),
            self.cached_access().branch_writes.is_empty(),
        ensures self.only_betree(),
    {
        assert(self.branch_reads.dom()
            == self.loaded_branch_reads().dom());
        assert(self.branch_writes.dom()
            == self.loaded_branch_writes().dom());
    }

    pub proof fn cached_only_branch_is_only_branch(self)
        requires
            self.cached_access().betree_reads.is_empty(),
            self.cached_access().betree_writes.is_empty(),
        ensures self.only_branch(),
    {
        assert(self.betree_reads.dom()
            == self.loaded_betree_reads().dom());
        assert(self.betree_writes.dom()
            == self.loaded_betree_writes().dom());
    }

    pub proof fn cached_read_only_is_read_only(self)
        requires
            self.cached_access().betree_writes.is_empty(),
            self.cached_access().branch_writes.is_empty(),
        ensures self.read_only(),
    {
        assert(self.betree_writes.dom()
            == self.loaded_betree_writes().dom());
        assert(self.branch_writes.dom()
            == self.loaded_branch_writes().dom());
    }

    pub proof fn cached_branch_writes_empty(self)
        requires self.cached_access().branch_writes.is_empty(),
        ensures self.branch_writes.is_empty(),
    {
        assert(self.branch_writes.dom()
            == self.loaded_branch_writes().dom());
    }

    pub proof fn cached_wf_is_wf(self)
        requires
            self.cached_access().betree_reads.dom().disjoint(
                self.cached_access().branch_reads.dom(),
            ),
            self.cached_access().betree_writes.dom().disjoint(
                self.cached_access().branch_writes.dom(),
            ),
        ensures self.wf(),
    {
        assert(self.betree_reads.dom()
            == self.loaded_betree_reads().dom());
        assert(self.branch_reads.dom()
            == self.loaded_branch_reads().dom());
        assert(self.betree_writes.dom()
            == self.loaded_betree_writes().dom());
        assert(self.branch_writes.dom()
            == self.loaded_branch_writes().dom());
    }

    pub proof fn cached_read_only_shape(self)
        requires self.read_only(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            betree_reads: self.loaded_betree_reads(),
            branch_reads: self.loaded_branch_reads(),
            betree_writes: Map::empty(),
            branch_writes: Map::empty(),
        }),
    {
        assert_maps_equal!(
            self.loaded_betree_writes(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_branch_writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_no_branch_writes_shape(self)
        requires self.branch_writes.is_empty(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            betree_reads: self.loaded_betree_reads(),
            branch_reads: self.loaded_branch_reads(),
            betree_writes: self.loaded_betree_writes(),
            branch_writes: Map::empty(),
        }),
    {
        assert_maps_equal!(
            self.loaded_branch_writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_only_betree_shape(self)
        requires self.only_betree(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            betree_reads: self.loaded_betree_reads(),
            betree_writes: self.loaded_betree_writes(),
            ..CachedBranchBetreeAccess::empty()
        }),
    {
        assert_maps_equal!(
            self.loaded_branch_reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_branch_writes(), Map::empty(), addr => {}
        );
    }

    pub proof fn cached_only_branch_shape(self)
        requires self.only_branch(),
        ensures self.cached_access() == (CachedBranchBetreeAccess {
            branch_reads: self.loaded_branch_reads(),
            branch_writes: self.loaded_branch_writes(),
            ..CachedBranchBetreeAccess::empty()
        }),
    {
        assert_maps_equal!(
            self.loaded_betree_reads(), Map::empty(), addr => {}
        );
        assert_maps_equal!(
            self.loaded_betree_writes(), Map::empty(), addr => {}
        );
    }
}

pub enum BranchBuildEvent {
    StagePage {
        addr: Address,
    },
    BulkSeal {
        root: Address,
        aux_ptr: Pointer,
    },
    // The mutable Append/Initialize/Grow/Split/Seal variants live in the
    // preserved CachingDiskBranch_v path for a possible branch-as-memtable.
}

impl BranchBuildEvent {
    pub open spec fn cached_event(self, access: PageAccess) -> CachedBulkBranchEvent {
        match self {
            BranchBuildEvent::StagePage{addr} => {
                CachedBulkBranchEvent::StagePage {
                    addr,
                    write_nodes: access.loaded_branch_writes(),
                }
            }
            BranchBuildEvent::BulkSeal{root, aux_ptr} => {
                CachedBulkBranchEvent::BulkSeal {
                    root,
                    aux_ptr,
                    write_nodes: access.loaded_branch_writes(),
                }
            }
        }
    }
}

pub open spec fn branch_build_event_of(
    event: CachedBulkBranchEvent,
) -> BranchBuildEvent {
    match event {
        CachedBulkBranchEvent::StagePage{addr, ..} =>
            BranchBuildEvent::StagePage{addr},
        CachedBulkBranchEvent::BulkSeal{root, aux_ptr, ..} =>
            BranchBuildEvent::BulkSeal{root, aux_ptr},
    }
}

state_machine! { CachingDiskBranchBetree {
    fields {
        pub disk: CachingDisk::State,
        pub betree: CachedBranchBetree::State,
    }

    pub enum Label {
        Query{end_lsn: LSN, key: Key, value: Value, access: PageAccess},
        Put{puts: MsgHistory},
        FreezeAs{image: FrozenBranchBetree},
        Internal,
        InternalAccess{access: PageAccess},
        InternalAllocAccess{
            allocs: Set<AU>,
            deallocs: Set<AU>,
            guard_aus: Set<AU>,
            access: PageAccess,
        },
    }

    init! { initialize(
        disk: CachingDisk::State,
        betree: CachedBranchBetree::State,
    ) {
        require disk.inv();
        require exists |config: CachedBranchBetree::Config|
            CachedBranchBetree::State::init_by(betree, config);

        init disk = disk;
        init betree = betree;
    }}

    transition! { disk_internal(
        lbl: Label,
        new_disk: CachingDisk::State,
    ) {
        require lbl is Internal;
        require CachingDisk::State::next(
            pre.disk, new_disk, CachingDisk::Label::Internal{},
        );

        update disk = new_disk;
    }}

    transition! { query(
        lbl: Label,
    ) {
        require let Label::Query{end_lsn, key, value, access} = lbl;
        require access.wf();
        require access.read_only();
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads: access.reads(), writes: access.writes()},
        );
        require CachedBranchBetree::State::next(
            pre.betree,
            pre.betree,
            CachedBranchBetree::Label::Query{
                end_lsn,
                key,
                value,
                access: access.cached_access(),
            },
        );
    }}

    transition! { put(lbl: Label, new_betree: CachedBranchBetree::State) {
        require let Label::Put{puts} = lbl;
        require CachedBranchBetree::State::next(
            pre.betree, new_betree, CachedBranchBetree::Label::Put{puts},
        );

        update betree = new_betree;
    }}

    transition! { freeze_as(lbl: Label) {
        require let Label::FreezeAs{image} = lbl;
        require CachedBranchBetree::State::next(
            pre.betree, pre.betree, CachedBranchBetree::Label::FreezeAs{image},
        );
    }}

    transition! { internal_access(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
    ) {
        require let Label::InternalAccess{access} = lbl;
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{
                reads: access.reads(),
                writes: access.writes(),
            },
        );
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAccess{
                access: access.cached_access(),
            },
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { internal_alloc_access(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
    ) {
        require let Label::InternalAllocAccess{
            allocs, deallocs, guard_aus, access,
        } = lbl;
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::next(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAllocAccess{
                allocs, deallocs, access: access.cached_access(),
            },
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { internal_noop(lbl: Label) {
        require lbl is Internal;
        require CachedBranchBetree::State::next(
            pre.betree, pre.betree, CachedBranchBetree::Label::Internal,
        );
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        self.disk.inv()
    }

    // ---------------------------------------------------------------------
    // Inductive invariant proofs
    // ---------------------------------------------------------------------

    #[inductive(initialize)]
    fn initialize_inductive(
        post: Self,
        disk: CachingDisk::State,
        betree: CachedBranchBetree::State,
    ) {
        assert(post.disk == disk);
    }

    #[inductive(disk_internal)]
    fn disk_internal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_disk: CachingDisk::State,
    ) {
        CachingDisk::State::inv_next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Internal{},
        );
        assert(post.disk == new_disk);
    }

    #[inductive(query)]
    fn query_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
    ) {
        assert(post.disk == pre.disk);
    }

    #[inductive(put)]
    fn put_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        assert(post.disk == pre.disk);
    }

    #[inductive(freeze_as)]
    fn freeze_as_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.disk == pre.disk);
    }

    #[inductive(internal_access)]
    fn internal_access_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
    ) {
        let access = lbl.arrow_InternalAccess_access();
        CachingDisk::State::inv_next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{
                reads: access.reads(),
                writes: access.writes(),
            },
        );
        assert(post.disk == new_disk);
    }

    #[inductive(internal_alloc_access)]
    fn internal_alloc_access_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
    ) {
        let access = lbl.arrow_InternalAllocAccess_access();
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAllocAccess_allocs(),
            lbl.arrow_InternalAllocAccess_deallocs(),
            lbl.arrow_InternalAllocAccess_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.disk == pre.disk);
    }

    pub proof fn put_effect(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    )
        requires CachingDiskBranchBetree::State::put(
            pre, post, lbl, new_betree,
        ),
        ensures
            post.disk == pre.disk,
            post.betree == new_betree,
            CachedBranchBetree::State::next(
                pre.betree, new_betree, CachedBranchBetree::Label::Put{
                    puts: lbl.arrow_Put_puts(),
                },
            ),
    {
    }

    pub proof fn initialize_from_cached(
        post: Self,
        disk: CachingDisk::State,
        betree: CachedBranchBetree::State,
        root: Pointer,
        seq_end: LSN,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
    )
        requires
            disk.inv(),
            post.disk == disk,
            post.betree == betree,
            CachedBranchBetree::State::initialize(
                betree,
                root,
                seq_end,
                betree_aus,
                branch_aus,
                branch_summary,
            ),
        ensures CachingDiskBranchBetree::State::initialize(
            post, disk, betree,
        ),
    {
        CachedBranchBetree::State::initialize_is_init_by(
            betree,
            root,
            seq_end,
            betree_aus,
            branch_aus,
            branch_summary,
        );
        assert(exists |config: CachedBranchBetree::Config|
            CachedBranchBetree::State::init_by(betree, config));
    }

    pub proof fn freeze_as_effect(pre: Self, post: Self, lbl: Label)
        requires CachingDiskBranchBetree::State::freeze_as(pre, post, lbl),
        ensures
            post == pre,
            CachedBranchBetree::State::next(
                pre.betree,
                pre.betree,
                CachedBranchBetree::Label::FreezeAs{
                    image: lbl.arrow_FreezeAs_image(),
                },
            ),
    {
    }

    pub proof fn internal_access_effect(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
    )
        requires CachingDiskBranchBetree::State::internal_access(
            pre, post, lbl, new_betree, new_disk,
        ),
        ensures
            lbl is InternalAccess,
            post.betree == new_betree,
            post.disk == new_disk,
            CachingDisk::State::next(
                pre.disk,
                new_disk,
                CachingDisk::Label::Access{
                    reads: lbl.arrow_InternalAccess_access().reads(),
                    writes: lbl.arrow_InternalAccess_access().writes(),
                },
            ),
            CachedBranchBetree::State::next(
                pre.betree,
                new_betree,
                CachedBranchBetree::Label::InternalAccess{
                    access: lbl.arrow_InternalAccess_access().cached_access(),
                },
            ),
    {
    }

    pub proof fn internal_alloc_access_effect(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
    )
        requires CachingDiskBranchBetree::State::internal_alloc_access(
            pre, post, lbl, new_betree, new_disk,
        ),
        ensures
            lbl is InternalAllocAccess,
            post.betree == new_betree,
            post.disk == new_disk,
            disk_access_for_alloc(
                pre.disk,
                new_disk,
                lbl.arrow_InternalAllocAccess_allocs(),
                lbl.arrow_InternalAllocAccess_deallocs(),
                lbl.arrow_InternalAllocAccess_guard_aus(),
                lbl.arrow_InternalAllocAccess_access().reads(),
                lbl.arrow_InternalAllocAccess_access().writes(),
            ),
            CachedBranchBetree::State::next(
                pre.betree,
                new_betree,
                CachedBranchBetree::Label::InternalAllocAccess{
                    allocs: lbl.arrow_InternalAllocAccess_allocs(),
                    deallocs: lbl.arrow_InternalAllocAccess_deallocs(),
                    access: lbl.arrow_InternalAllocAccess_access().cached_access(),
                },
            ),
    {
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CachingDiskBranchBetree::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);

        let step = choose |step: CachingDiskBranchBetree::Step|
            CachingDiskBranchBetree::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranchBetree::Step::disk_internal(new_disk) => {
                CachingDiskBranchBetree::State::disk_internal_inductive(
                    pre, post, lbl, new_disk,
                );
            }
            CachingDiskBranchBetree::Step::query() => {
                CachingDiskBranchBetree::State::query_inductive(
                    pre, post, lbl,
                );
            }
            CachingDiskBranchBetree::Step::put(new_betree) => {
                CachingDiskBranchBetree::State::put_inductive(
                    pre, post, lbl, new_betree,
                );
            }
            CachingDiskBranchBetree::Step::freeze_as() => {
                CachingDiskBranchBetree::State::freeze_as_inductive(
                    pre, post, lbl,
                );
            }
            CachingDiskBranchBetree::Step::internal_access(
                new_betree, new_disk,
            ) => {
                CachingDiskBranchBetree::State::internal_access_inductive(
                    pre, post, lbl, new_betree, new_disk,
                );
            }
            CachingDiskBranchBetree::Step::internal_alloc_access(
                new_betree, new_disk,
            ) => {
                CachingDiskBranchBetree::State::internal_alloc_access_inductive(
                    pre, post, lbl, new_betree, new_disk,
                );
            }
            CachingDiskBranchBetree::Step::internal_noop() => {
                CachingDiskBranchBetree::State::internal_noop_inductive(
                    pre, post, lbl,
                );
            }
            _ => { assert(false); }
        }
    }
}}

} // verus!
