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
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
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
use crate::implementation::AllocationBranchStack_v::tight_branch_in_loose_disk;
use crate::implementation::CachedBranchBetree_v::{
    CachedAllocationBranch, CachedAllocationBranchEvent, CachedBranchBetree,
    FrozenBranchBetree, LoadedBetree, LoadedBetreePath, LoadedBetreeQueryReceipt,
};
use crate::implementation::CachingDisk_v::{
    CachingDisk, addresses_in_aus,
};
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};

verus! {

// The concrete Betree-node marshaller has not been introduced yet. Keeping the
// decoder abstract makes that missing implementation boundary explicit while
// still giving raw pages one stable Betree interpretation in this model.
pub uninterp spec fn raw_page_to_betree_node(raw_page: RawPage) -> BetreeNode;

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
}

pub enum BranchBuildEvent {
    Append {
        receipt: LoadedPathReceipt,
        keys: Seq<Key>,
        msgs: Seq<Message>,
    },
    Initialize {
        init_root: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
    },
    Grow {
        new_root_addr: Address,
    },
    Split {
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
    },
    Seal {
        aux_ptr: Pointer,
    },
}

impl BranchBuildEvent {
    pub open spec fn cached_event(self, access: PageAccess) -> CachedAllocationBranchEvent {
        match self {
            BranchBuildEvent::Append{receipt, keys, msgs} => {
                CachedAllocationBranchEvent::Append {
                    receipt,
                    keys,
                    msgs,
                    read_nodes: access.loaded_branch_reads(),
                    write_nodes: access.loaded_branch_writes(),
                }
            }
            BranchBuildEvent::Initialize{init_root, keys, msgs} => {
                CachedAllocationBranchEvent::Initialize {
                    init_root,
                    keys,
                    msgs,
                    write_nodes: access.loaded_branch_writes(),
                }
            }
            BranchBuildEvent::Grow{new_root_addr} => {
                CachedAllocationBranchEvent::Grow {
                    new_root_addr,
                    read_nodes: access.loaded_branch_reads(),
                    write_nodes: access.loaded_branch_writes(),
                }
            }
            BranchBuildEvent::Split{new_child_addr, receipt, split_arg} => {
                CachedAllocationBranchEvent::Split {
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes: access.loaded_branch_reads(),
                    write_nodes: access.loaded_branch_writes(),
                }
            }
            BranchBuildEvent::Seal{aux_ptr} => {
                CachedAllocationBranchEvent::Seal {
                    aux_ptr,
                    read_nodes: access.loaded_branch_reads(),
                    write_nodes: access.loaded_branch_writes(),
                }
            }
        }
    }
}

state_machine! { CachingDiskBranchBetree {
    fields {
        pub disk: CachingDisk::State,
        pub betree: CachedBranchBetree::State,
    }

    pub enum Label {
        Query{end_lsn: LSN, key: Key, value: Value},
        Put{puts: MsgHistory},
        FreezeAs{image: FrozenBranchBetree},
        Internal,
        InternalAlloc{
            allocs: Set<AU>,
            deallocs: Set<AU>,
            guard_aus: Set<AU>,
        },
    }

    init! { initialize(
        disk: CachingDisk::State,
        betree: CachedBranchBetree::State,
        root: Pointer,
        seq_end: LSN,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
    ) {
        require disk.inv();
        require CachedBranchBetree::State::initialize(
            betree, root, seq_end, betree_aus, branch_aus, branch_summary,
        );

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
        receipt: LoadedBetreeQueryReceipt,
        access: PageAccess,
    ) {
        require let Label::Query{end_lsn, key, value} = lbl;
        require access.wf();
        require access.read_only();
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads: access.reads(), writes: access.writes()},
        );
        require CachedBranchBetree::State::query(
            pre.betree,
            pre.betree,
            CachedBranchBetree::Label::Query{end_lsn, key, value},
            receipt,
            access.loaded_betree_reads(),
            access.loaded_branch_reads(),
        );
    }}

    transition! { put(lbl: Label, new_betree: CachedBranchBetree::State) {
        require let Label::Put{puts} = lbl;
        require CachedBranchBetree::State::put(
            pre.betree, new_betree, CachedBranchBetree::Label::Put{puts},
        );

        update betree = new_betree;
    }}

    transition! { freeze_as(lbl: Label) {
        require let Label::FreezeAs{image} = lbl;
        require CachedBranchBetree::State::freeze_as(
            pre.betree, pre.betree, CachedBranchBetree::Label::FreezeAs{image},
        );
    }}

    transition! { branch_begin(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require CachedBranchBetree::State::branch_begin(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
        );

        update betree = new_betree;
    }}

    transition! { branch_fill(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedAllocationBranch,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require CachedBranchBetree::State::branch_build(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            idx,
            post_branch,
            CachedAllocationBranchEvent::AllocFill{},
        );
        require disk_extend_for_alloc(pre.disk, new_disk, allocs);

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { branch_build(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedAllocationBranch,
        event: BranchBuildEvent,
        access: PageAccess,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require access.only_branch();
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::branch_build(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            idx,
            post_branch,
            event.cached_event(access),
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { branch_abort(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require CachedBranchBetree::State::branch_abort(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            idx,
        );
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Forget{
                aus: deallocs - guard_aus,
            },
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { flush_memtable(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        branch_idx: int,
        new_root_addr: Address,
        access: PageAccess,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require access.wf();
        require access.branch_writes.is_empty();
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::flush_memtable(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            branch_idx,
            new_root_addr,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
            access.loaded_branch_reads(),
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { grow(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        new_root_addr: Address,
        access: PageAccess,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require access.only_betree();
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::grow(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            new_root_addr,
            access.loaded_betree_writes(),
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { split(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        path: LoadedBetreePath,
        request: SplitRequest,
        new_addrs: SplitAddrs,
        path_addrs: PathAddrs,
        access: PageAccess,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require access.only_betree();
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::split(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            path,
            request,
            new_addrs,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { flush(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        path: LoadedBetreePath,
        child_idx: nat,
        buffer_gc: nat,
        new_addrs: TwoAddrs,
        path_addrs: PathAddrs,
        access: PageAccess,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require access.only_betree();
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::flush(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { compact_begin(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        access: PageAccess,
    ) {
        require lbl is Internal;
        require access.only_betree();
        require access.read_only();
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads: access.reads(), writes: access.writes()},
        );
        require CachedBranchBetree::State::compact_begin(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::Internal,
            path,
            start,
            end,
            access.loaded_betree_reads(),
        );

        update betree = new_betree;
    }}

    transition! { compact_abort(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        input_idx: int,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require CachedBranchBetree::State::compact_abort(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            input_idx,
        );
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Forget{
                aus: deallocs - guard_aus,
            },
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { compact_complete(
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        input_idx: int,
        branch_idx: int,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        new_node_addr: Address,
        path_addrs: PathAddrs,
        access: PageAccess,
    ) {
        require let Label::InternalAlloc{
            allocs, deallocs, guard_aus,
        } = lbl;
        require access.wf();
        require access.branch_writes.is_empty();
        require disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        );
        require CachedBranchBetree::State::compact_complete(
            pre.betree,
            new_betree,
            CachedBranchBetree::Label::InternalAlloc{allocs, deallocs},
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
            access.loaded_branch_reads(),
        );

        update betree = new_betree;
        update disk = new_disk;
    }}

    transition! { internal_noop(lbl: Label) {
        require lbl is Internal;
        require CachedBranchBetree::State::internal_noop(
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
        root: Pointer,
        seq_end: LSN,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
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
        receipt: LoadedBetreeQueryReceipt,
        access: PageAccess,
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

    #[inductive(branch_begin)]
    fn branch_begin_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
    ) {
        assert(post.disk == pre.disk);
    }

    #[inductive(branch_fill)]
    fn branch_fill_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedAllocationBranch,
    ) {
        assert(post.disk == new_disk);
    }

    #[inductive(branch_build)]
    fn branch_build_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedAllocationBranch,
        event: BranchBuildEvent,
        access: PageAccess,
    ) {
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(branch_abort)]
    fn branch_abort_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
    ) {
        CachingDisk::State::inv_next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Forget{
                aus: lbl.arrow_InternalAlloc_deallocs()
                    - lbl.arrow_InternalAlloc_guard_aus(),
            },
        );
        assert(post.disk == new_disk);
    }

    #[inductive(flush_memtable)]
    fn flush_memtable_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        branch_idx: int,
        new_root_addr: Address,
        access: PageAccess,
    ) {
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(grow)]
    fn grow_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        new_root_addr: Address,
        access: PageAccess,
    ) {
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(split)]
    fn split_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        path: LoadedBetreePath,
        request: SplitRequest,
        new_addrs: SplitAddrs,
        path_addrs: PathAddrs,
        access: PageAccess,
    ) {
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(flush)]
    fn flush_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        path: LoadedBetreePath,
        child_idx: nat,
        buffer_gc: nat,
        new_addrs: TwoAddrs,
        path_addrs: PathAddrs,
        access: PageAccess,
    ) {
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(compact_begin)]
    fn compact_begin_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        access: PageAccess,
    ) {
        assert(post.disk == pre.disk);
    }

    #[inductive(compact_abort)]
    fn compact_abort_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        input_idx: int,
    ) {
        CachingDisk::State::inv_next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Forget{
                aus: lbl.arrow_InternalAlloc_deallocs()
                    - lbl.arrow_InternalAlloc_guard_aus(),
            },
        );
        assert(post.disk == new_disk);
    }

    #[inductive(compact_complete)]
    fn compact_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        input_idx: int,
        branch_idx: int,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        new_node_addr: Address,
        path_addrs: PathAddrs,
        access: PageAccess,
    ) {
        disk_access_for_alloc_preserves_inv(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_guard_aus(),
            access.reads(),
            access.writes(),
        );
        assert(post.disk == new_disk);
    }

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.disk == pre.disk);
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
            CachingDiskBranchBetree::Step::query(receipt, access) => {
                CachingDiskBranchBetree::State::query_inductive(
                    pre, post, lbl, receipt, access,
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
            CachingDiskBranchBetree::Step::branch_begin(new_betree) => {
                CachingDiskBranchBetree::State::branch_begin_inductive(
                    pre, post, lbl, new_betree,
                );
            }
            CachingDiskBranchBetree::Step::branch_fill(
                new_betree,
                new_disk,
                idx,
                post_branch,
            ) => {
                CachingDiskBranchBetree::State::branch_fill_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    idx,
                    post_branch,
                );
            }
            CachingDiskBranchBetree::Step::branch_build(
                new_betree,
                new_disk,
                idx,
                post_branch,
                event,
                access,
            ) => {
                CachingDiskBranchBetree::State::branch_build_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    idx,
                    post_branch,
                    event,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::branch_abort(
                new_betree,
                new_disk,
                idx,
            ) => {
                CachingDiskBranchBetree::State::branch_abort_inductive(
                    pre, post, lbl, new_betree, new_disk, idx,
                );
            }
            CachingDiskBranchBetree::Step::flush_memtable(
                new_betree,
                new_disk,
                branch_idx,
                new_root_addr,
                access,
            ) => {
                CachingDiskBranchBetree::State::flush_memtable_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    branch_idx,
                    new_root_addr,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::grow(
                new_betree,
                new_disk,
                new_root_addr,
                access,
            ) => {
                CachingDiskBranchBetree::State::grow_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    new_root_addr,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::split(
                new_betree,
                new_disk,
                path,
                request,
                new_addrs,
                path_addrs,
                access,
            ) => {
                CachingDiskBranchBetree::State::split_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    path,
                    request,
                    new_addrs,
                    path_addrs,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::flush(
                new_betree,
                new_disk,
                path,
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
                access,
            ) => {
                CachingDiskBranchBetree::State::flush_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    path,
                    child_idx,
                    buffer_gc,
                    new_addrs,
                    path_addrs,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::compact_begin(
                new_betree,
                path,
                start,
                end,
                access,
            ) => {
                CachingDiskBranchBetree::State::compact_begin_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    path,
                    start,
                    end,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::compact_abort(
                new_betree,
                new_disk,
                input_idx,
            ) => {
                CachingDiskBranchBetree::State::compact_abort_inductive(
                    pre, post, lbl, new_betree, new_disk, input_idx,
                );
            }
            CachingDiskBranchBetree::Step::compact_complete(
                new_betree,
                new_disk,
                input_idx,
                branch_idx,
                path,
                start,
                end,
                new_node_addr,
                path_addrs,
                access,
            ) => {
                CachingDiskBranchBetree::State::compact_complete_inductive(
                    pre,
                    post,
                    lbl,
                    new_betree,
                    new_disk,
                    input_idx,
                    branch_idx,
                    path,
                    start,
                    end,
                    new_node_addr,
                    path_addrs,
                    access,
                );
            }
            CachingDiskBranchBetree::Step::internal_noop() => {
                CachingDiskBranchBetree::State::internal_noop_inductive(
                    pre, post, lbl,
                );
            }
            _ => {
                assert(false);
            }
        }
    }
}}

} // verus!
