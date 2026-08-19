// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_multisets_equal;
use vstd::assert_seqs_equal;
use vstd::multiset::Multiset;
use vstd::seq_lib::{lemma_multiset_commutative, to_multiset_build};

use crate::betree::LinkedBetree_v::{Addrs, PathAddrs, SplitAddrs};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::allocation_layer::Likes_v::{
    to_au_likes, to_au_likes_commutative_over_add,
    to_au_likes_singleton,
};
use crate::allocation_layer::LikesBetree_v::Likeable;
use crate::disk::GenericDisk_v::{
    AU, Address, Pointer, seq_addrs_disjoint_aus,
};
use crate::implementation::BetreePageImpl_v::marshall_betree_node_page;
use crate::implementation::BetreePathImpl_v::{
    BetreePathWorkspace, betree_path_receipt_wf,
};
use crate::implementation::BetreePageImpl_v::betree_node_addr;
use crate::implementation::BetreeStructuralPageImpl_v::{
    IBetreeSplitRequest, build_ancestor_replacement,
    build_split_node_pages, split_parent_view,
};
use crate::implementation::BetreeWriteBatchImpl_v::{
    BetreeWriteEntry, betree_node_writes, betree_raw_writes,
    betree_node_writes_push, betree_raw_writes_dom,
    betree_raw_writes_to_nodes,
    betree_write_entries_push, betree_write_entries_wf,
};
use crate::implementation::CachedBranchBetree_v::{
    LoadedBetree, LoadedBetreePath, LoadedBetreePathLine,
    added_path_likes,
    replacement_root, split_replacement, substitute_writes,
};
use crate::implementation::CachingDiskBranchBetree_v::to_betree_nodes;
use crate::implementation::Cache_v::Cache;
use crate::marshalling::IBetreeNodeFormat_v::raw_page_to_betree_node;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::ImplDisk_t::IAU;
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::AuLikesImpl_v::{
    seq_to_au_likes, seq_to_au_likes_push,
};

verus! {

pub open spec fn iaddr_views(addrs: Seq<IAddress>) -> Seq<Address> {
    Seq::new(addrs.len(), |i: int| addrs[i]@)
}

pub fn iaddress_aus(addrs: &Vec<IAddress>) -> (out: Vec<IAU>)
    ensures
        out@.len() == addrs@.len(),
        forall |i: int| 0 <= i < out@.len()
            ==> (#[trigger] out@[i]) as nat == addrs@[i]@.au,
{
    let mut out = Vec::<IAU>::new();
    let mut index = 0usize;
    while index < addrs.len()
        invariant
            index <= addrs.len(),
            out@.len() == index,
            forall |i: int| 0 <= i < out@.len()
                ==> (#[trigger] out@[i]) as nat == addrs@[i]@.au,
        decreases addrs.len() - index,
    {
        out.push(addrs[index].au);
        index += 1;
    }
    out
}

pub proof fn iaddress_aus_likes(
    addrs: Seq<IAddress>,
    aus: Seq<IAU>,
)
    requires
        aus.len() == addrs.len(),
        forall |i: int| 0 <= i < aus.len()
            ==> (#[trigger] aus[i]) as nat == addrs[i]@.au,
    ensures
        seq_to_au_likes(aus)
            =~= to_au_likes(iaddr_views(addrs).to_multiset()),
    decreases addrs.len(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    if addrs.len() == 0 {
        assert(aus.len() == 0);
        assert(seq_to_au_likes(aus) == Multiset::<AU>::empty());
        assert(iaddr_views(addrs).len() == 0);
        assert(iaddr_views(addrs) == Seq::<Address>::empty());
        iaddr_views(addrs).to_multiset_ensures();
        assert_multisets_equal!(
            iaddr_views(addrs).to_multiset(),
            Multiset::<Address>::empty(),
            addr => {}
        );
        crate::allocation_layer::Likes_v::to_au_likes_empty();
    } else {
        let addrs_prefix = addrs.drop_last();
        let aus_prefix = aus.drop_last();
        assert(aus_prefix.len() == addrs_prefix.len());
        assert forall |i: int| 0 <= i < aus_prefix.len()
            implies (#[trigger] aus_prefix[i]) as nat
                == addrs_prefix[i]@.au by {
            assert(aus_prefix[i] == aus[i]);
            assert(addrs_prefix[i] == addrs[i]);
        }
        iaddress_aus_likes(addrs_prefix, aus_prefix);
        seq_to_au_likes_push(aus_prefix, aus.last());
        to_au_likes_singleton(addrs.last()@);
        to_au_likes_commutative_over_add(
            iaddr_views(addrs_prefix).to_multiset(),
            Multiset::singleton(addrs.last()@),
        );
        assert(iaddr_views(addrs)
            == iaddr_views(addrs_prefix).push(addrs.last()@)) by {
            assert_seqs_equal!(
                iaddr_views(addrs),
                iaddr_views(addrs_prefix).push(addrs.last()@),
                i => {}
            );
        }
        to_multiset_build(
            iaddr_views(addrs_prefix),
            addrs.last()@,
        );
        assert(iaddr_views(addrs).to_multiset()
            == iaddr_views(addrs_prefix).to_multiset()
                .add(Multiset::singleton(addrs.last()@)));
        assert(aus.last() as nat == addrs.last()@.au);
        assert(seq_to_au_likes(aus)
            == seq_to_au_likes(aus_prefix).insert(aus.last() as nat));
        assert_multisets_equal!(
            seq_to_au_likes(aus),
            to_au_likes(iaddr_views(addrs).to_multiset()),
            au => {}
        );
    }
    assert_multisets_equal!(
        seq_to_au_likes(aus),
        to_au_likes(iaddr_views(addrs).to_multiset()),
        au => {}
    );
}

pub proof fn split_discard_au_likes(
    path_addrs: Seq<IAddress>,
    child: IAddress,
    old_addresses: Seq<IAddress>,
    old_aus: Seq<IAU>,
)
    requires
        old_addresses == path_addrs.push(child),
        old_aus.len() == old_addresses.len(),
        forall |i: int| 0 <= i < old_aus.len()
            ==> (#[trigger] old_aus[i]) as nat
                == old_addresses[i]@.au,
    ensures
        seq_to_au_likes(old_aus) =~= to_au_likes(
            iaddr_views(path_addrs).to_multiset().insert(child@),
        ),
{
    iaddress_aus_likes(old_addresses, old_aus);
    assert(iaddr_views(old_addresses)
        == iaddr_views(path_addrs).push(child@)) by {
        assert_seqs_equal!(
            iaddr_views(old_addresses),
            iaddr_views(path_addrs).push(child@),
            i => {}
        );
    }
    to_multiset_build(iaddr_views(path_addrs), child@);
    assert_multisets_equal!(
        iaddr_views(old_addresses).to_multiset(),
        iaddr_views(path_addrs).to_multiset().insert(child@),
        addr => {}
    );
}

proof fn finite_set_to_multiset_count<A>(set: Set<A>, value: A)
    requires set.finite(),
    ensures
        set.to_multiset().count(value)
            == if set.contains(value) { 1nat } else { 0nat },
    decreases set.len(),
{
    broadcast use vstd::set_lib::group_set_properties;

    if set.len() == 0 {
        set.lemma_len0_is_empty();
    } else {
        let chosen = set.choose();
        assert(set.contains(chosen));
        finite_set_to_multiset_count(set.remove(chosen), value);
        if value == chosen {
            assert(!set.remove(chosen).contains(value));
        } else {
            assert(set.remove(chosen).contains(value) == set.contains(value));
        }
    }
}

proof fn split_addrs_repr_likes(addrs: SplitAddrs)
    requires addrs.no_duplicates(),
    ensures addrs.repr().to_multiset() == addrs.likes(),
{
    assert forall |addr: Address|
        addrs.repr().to_multiset().count(addr) == addrs.likes().count(addr)
    by {
        finite_set_to_multiset_count(addrs.repr(), addr);
        if addr == addrs.left {
        } else if addr == addrs.right {
        } else if addr == addrs.parent {
        } else {
            assert(!addrs.repr().contains(addr));
        }
    };
}

proof fn split_destination_prefix_likes(addrs: SplitAddrs)
    ensures
        seq![addrs.left, addrs.right, addrs.parent].to_multiset()
            =~= addrs.likes(),
{
    broadcast use vstd::multiset::group_multiset_axioms;

    let empty = Seq::<Address>::empty();
    let one = seq![addrs.left];
    let two = seq![addrs.left, addrs.right];
    let three = seq![addrs.left, addrs.right, addrs.parent];
    assert(one == empty.push(addrs.left));
    assert(two == one.push(addrs.right));
    assert(three == two.push(addrs.parent));
    empty.to_multiset_ensures();
    assert(empty.to_multiset().len() == 0);
    assert(empty.to_multiset() =~= Multiset::<Address>::empty());
    to_multiset_build(empty, addrs.left);
    assert(one.to_multiset() =~= Multiset::singleton(addrs.left));
    to_multiset_build(one, addrs.right);
    assert(two.to_multiset() =~=
        Multiset::singleton(addrs.left)
            .add(Multiset::singleton(addrs.right)));
    to_multiset_build(two, addrs.parent);
    assert(three.to_multiset() =~=
        Multiset::singleton(addrs.left)
            .add(Multiset::singleton(addrs.right))
            .add(Multiset::singleton(addrs.parent)));
    assert(addrs.likes()
        == Multiset::singleton(addrs.parent).add(
            Multiset::singleton(addrs.left).add(
                Multiset::singleton(addrs.right)
            )
        ));
    assert(three.to_multiset() =~= addrs.likes());
}

pub proof fn split_added_au_likes(
    left: IAddress,
    right: IAddress,
    parent: IAddress,
    path_addrs: Seq<IAddress>,
    destinations: Seq<IAddress>,
    new_aus: Seq<IAU>,
)
    requires
        destinations == seq![left, right, parent] + path_addrs,
        new_aus.len() == destinations.len(),
        forall |i: int| 0 <= i < new_aus.len()
            ==> (#[trigger] new_aus[i]) as nat
                == destinations[i]@.au,
        left@ != right@,
        left@ != parent@,
        right@ != parent@,
    ensures
        seq_to_au_likes(new_aus) =~= to_au_likes(added_path_likes(
            SplitAddrs {
                left: left@,
                right: right@,
                parent: parent@,
            },
            iaddr_views(path_addrs),
        )),
{
    iaddress_aus_likes(destinations, new_aus);
    let split = SplitAddrs {
        left: left@,
        right: right@,
        parent: parent@,
    };
    assert(iaddr_views(destinations)
        == seq![left@, right@, parent@] + iaddr_views(path_addrs)) by {
        assert_seqs_equal!(
            iaddr_views(destinations),
            seq![left@, right@, parent@] + iaddr_views(path_addrs),
            i => {}
        );
    }
    let three = seq![left@, right@, parent@];
    split_destination_prefix_likes(split);
    split_addrs_repr_likes(split);
    assert(three.to_multiset() =~= split.repr().to_multiset());
    lemma_multiset_commutative(
        seq![left@, right@, parent@],
        iaddr_views(path_addrs),
    );
    assert_multisets_equal!(
        iaddr_views(destinations).to_multiset(),
        added_path_likes(split, iaddr_views(path_addrs)),
        addr => {}
    );
}

pub open spec fn iaddr_views_unique(addrs: Seq<IAddress>) -> bool {
    forall |i: int, j: int| #![trigger addrs[i], addrs[j]]
        0 <= i < addrs.len()
        && 0 <= j < addrs.len()
        && addrs[i]@ == addrs[j]@
        ==> i == j
}

pub proof fn iaddr_views_skip(
    addrs: Seq<IAddress>,
    start: int,
)
    requires 0 <= start <= addrs.len(),
    ensures
        iaddr_views(addrs.skip(start)) == iaddr_views(addrs).skip(start),
{
    assert_seqs_equal!(
        iaddr_views(addrs.skip(start)),
        iaddr_views(addrs).skip(start),
        i => {}
    );
}

proof fn unique_iaddr_before_suffix(
    addrs: Seq<IAddress>,
    index: int,
    start: int,
)
    requires
        iaddr_views_unique(addrs),
        0 <= index < start <= addrs.len(),
    ensures
        !iaddr_views(addrs).skip(start).to_set()
            .contains(addrs[index]@),
{
    if iaddr_views(addrs).skip(start).to_set().contains(addrs[index]@) {
        let suffix = iaddr_views(addrs).skip(start);
        let j = choose |j: int| 0 <= j < suffix.len()
            && suffix[j] == addrs[index]@;
        assert(suffix[j] == iaddr_views(addrs)[start + j]);
        assert(iaddr_views(addrs)[index] == addrs[index]@);
        assert(addrs[index]@ == addrs[start + j]@);
        assert(index == start + j);
        assert(false);
    }
}

pub open spec fn path_suffix(
    path: LoadedBetreePath,
    start: int,
) -> LoadedBetreePath
    recommends 0 <= start < path.lines.len(),
{
    LoadedBetreePath {
        key: path.key,
        root: path.lines[start].addr,
        lines: path.lines.skip(start),
    }
}

pub open spec fn cached_split_parent_wf(
    cache: Cache::State,
    current: Address,
    key: crate::spec::KeyType_t::Key,
    depth: nat,
    request: SplitRequest,
    left: Address,
    right: Address,
) -> bool
    decreases depth,
{
    if depth == 0 {
        forall |parent_raw: RawPage|
            #[trigger] cache.valid_read(current, parent_raw) ==> {
            let parent = raw_page_to_betree_node(parent_raw);
            let child_idx = request.get_child_idx();
            parent.valid_child_index(child_idx)
            && parent.children[child_idx as int] is Some ==> {
                let child_addr = parent.children[child_idx as int].unwrap();
                forall |child_raw: RawPage|
                    #[trigger] cache.valid_read(child_addr, child_raw) ==> {
                    let child = raw_page_to_betree_node(child_raw);
                    let can_split = match request {
                        SplitRequest::SplitLeaf { split_key, .. } => {
                            child.can_split_leaf(split_key)
                        },
                        SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                            child.can_split_index(child_pivot_idx)
                        },
                    };
                    &&& child.wf()
                    &&& can_split ==> split_parent_view(
                            parent,
                            child,
                            request,
                            left,
                            right,
                        ).wf()
                }
            }
        }
    } else {
        forall |raw: RawPage| #[trigger] cache.valid_read(current, raw) ==> {
            let node = raw_page_to_betree_node(raw);
            node.child_ptr(key) is Some ==> cached_split_parent_wf(
                cache,
                node.child_ptr(key).unwrap(),
                key,
                (depth - 1) as nat,
                request,
                left,
                right,
            )
        }
    }
}

pub proof fn cached_split_parent_wf_for_path(
    cache: Cache::State,
    path: LoadedBetreePath,
    path_reads: Map<Address, RawPage>,
    request: SplitRequest,
    left: Address,
    right: Address,
)
    requires
        path.valid_for(Some(path.root), to_betree_nodes(path_reads)),
        forall |i: int| 0 <= i < path.lines.len() - 1
            ==> (#[trigger] path.lines[i]).node.child_ptr(path.key)
                == Some(path.lines[i + 1].addr),
        forall |addr: Address| #[trigger] path_reads.contains_key(addr)
            ==> cache.valid_read(addr, path_reads[addr]),
        cached_split_parent_wf(
            cache,
            path.root,
            path.key,
            path.depth(),
            request,
            left,
            right,
        ),
    ensures {
        let parent = path.target().node;
        let child_idx = request.get_child_idx();
        parent.valid_child_index(child_idx)
        && parent.children[child_idx as int] is Some ==> {
            let child_addr = parent.children[child_idx as int].unwrap();
            forall |child_raw: RawPage|
                #[trigger] cache.valid_read(child_addr, child_raw) ==> {
                let child = raw_page_to_betree_node(child_raw);
                let can_split = match request {
                    SplitRequest::SplitLeaf { split_key, .. } => {
                        child.can_split_leaf(split_key)
                    },
                    SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                        child.can_split_index(child_pivot_idx)
                    },
                };
                &&& child.wf()
                &&& can_split ==> split_parent_view(
                        parent,
                        child,
                        request,
                        left,
                        right,
                    ).wf()
            }
        }
    },
    decreases path.depth(),
{
    let raw = path_reads[path.lines[0].addr];
    let node = raw_page_to_betree_node(raw);
    assert(path.needed_addrs().contains(path.lines[0].addr)) by {
        assert(exists |i: int| 0 <= i < path.lines.len()
            && #[trigger] path.lines[i].addr == path.lines[0].addr) by {
            assert(path.lines[0].addr == path.lines[0].addr);
        }
    }
    assert(path_reads.contains_key(path.lines[0].addr));
    assert(to_betree_nodes(path_reads)[path.lines[0].addr]
        == path.lines[0].node);
    assert(node == path.lines[0].node);
    assert(cache.valid_read(path.lines[0].addr, raw));
    if path.depth() > 0 {
        let tail = path.tail();

        assert(path.wf());
        assert(path.lines.len() > 1);
        assert(0 < path.lines.len() - 1);
        assert(path.lines[0].wf());
        assert(path.lines[1].wf());
        assert(path.lines[1] == path.lines[1]);
        assert(path.lines[1].addr == path.lines[1].addr);
        assert(path.lines[0].node.child_ptr(path.key)
            == Some(path.lines[1].addr));
        assert(path.lines[0].node.child_ptr(path.key) is Some);
        assert(path.lines[0].node.child_ptr(path.key).unwrap()
            == path.lines[1].addr);
        assert(node == path.lines[0].node);
        assert(node.child_ptr(path.key) is Some);
        assert(node.child_ptr(path.key).unwrap() == tail.root);
        assert(cached_split_parent_wf(
            cache,
            tail.root,
            tail.key,
            tail.depth(),
            request,
            left,
            right,
        ));
        assert(tail.wf()) by {
            path_suffix_facts(path, 1);
            assert(path_suffix(path, 1) == tail);
        }
        assert(tail.needed_addrs() <= path.needed_addrs()) by {
            assert forall |addr: Address|
                #[trigger] tail.needed_addrs().contains(addr)
                implies path.needed_addrs().contains(addr) by {
                let i = choose |i: int| 0 <= i < tail.lines.len()
                    && #[trigger] tail.lines[i].addr == addr;
                assert(tail.lines[i] == path.lines[i + 1]);
                assert(exists |j: int| 0 <= j < path.lines.len()
                    && #[trigger] path.lines[j].addr == addr) by {
                    assert(path.lines[i + 1].addr == addr);
                }
            }
        }
        assert forall |i: int| 0 <= i < tail.lines.len()
            implies {
                &&& to_betree_nodes(path_reads)
                    .contains_key((#[trigger] tail.lines[i]).addr)
                &&& to_betree_nodes(path_reads)[tail.lines[i].addr]
                    == tail.lines[i].node
            } by {
            assert(tail.lines[i] == path.lines[i + 1]);
        }
        assert forall |i: int| 0 <= i < tail.lines.len() - 1
            implies (#[trigger] tail.lines[i]).node.child_ptr(tail.key)
                == Some(tail.lines[i + 1].addr) by {
            assert(tail.lines[i] == path.lines[i + 1]);
            assert(tail.lines[i + 1] == path.lines[i + 2]);
        }
        assert(tail.valid_for(
            Some(tail.root),
            to_betree_nodes(path_reads),
        ));
        cached_split_parent_wf_for_path(
            cache,
            tail,
            path_reads,
            request,
            left,
            right,
        );
    } else {
        assert(path.lines.len() == 1);
        assert(path.target() == path.lines[0]);
        let parent = path.target().node;
        let child_idx = request.get_child_idx();
        if parent.valid_child_index(child_idx)
            && parent.children[child_idx as int] is Some
        {
            let child_addr = parent.children[child_idx as int].unwrap();
            assert forall |child_raw: RawPage|
                #[trigger] cache.valid_read(child_addr, child_raw)
                implies {
                    let child = raw_page_to_betree_node(child_raw);
                    let can_split = match request {
                        SplitRequest::SplitLeaf { split_key, .. } => {
                            child.can_split_leaf(split_key)
                        },
                        SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                            child.can_split_index(child_pivot_idx)
                        },
                    };
                    &&& child.wf()
                    &&& can_split ==> split_parent_view(
                            parent,
                            child,
                            request,
                            left,
                            right,
                        ).wf()
                } by {
            }
        }
    }
}

pub proof fn cached_split_selected_child_wf(
    cache: Cache::State,
    path: LoadedBetreePath,
    path_reads: Map<Address, RawPage>,
    request: SplitRequest,
    left: Address,
    right: Address,
    child_addr: Address,
    child_raw: RawPage,
)
    requires
        path.valid_for(Some(path.root), to_betree_nodes(path_reads)),
        forall |i: int| 0 <= i < path.lines.len() - 1
            ==> (#[trigger] path.lines[i]).node.child_ptr(path.key)
                == Some(path.lines[i + 1].addr),
        forall |addr: Address| #[trigger] path_reads.contains_key(addr)
            ==> cache.valid_read(addr, path_reads[addr]),
        cached_split_parent_wf(
            cache,
            path.root,
            path.key,
            path.depth(),
            request,
            left,
            right,
        ),
        path.target().node.valid_child_index(request.get_child_idx()),
        path.target().node.children[request.get_child_idx() as int]
            == Some(child_addr),
        cache.valid_read(child_addr, child_raw),
    ensures {
        let child = raw_page_to_betree_node(child_raw);
        let can_split = match request {
            SplitRequest::SplitLeaf { split_key, .. } => {
                child.can_split_leaf(split_key)
            },
            SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                child.can_split_index(child_pivot_idx)
            },
        };
        &&& child.wf()
        &&& can_split ==> split_parent_view(
                path.target().node,
                child,
                request,
                left,
                right,
            ).wf()
    },
{
    cached_split_parent_wf_for_path(
        cache,
        path,
        path_reads,
        request,
        left,
        right,
    );
    assert(path.target().node.children[
        request.get_child_idx() as int
    ].unwrap() == child_addr);
}

pub proof fn disjoint_au_views_are_unique(addrs: Seq<IAddress>)
    requires seq_addrs_disjoint_aus(iaddr_views(addrs)),
    ensures iaddr_views_unique(addrs),
{
    assert forall |i: int, j: int| #![trigger addrs[i], addrs[j]]
        0 <= i < addrs.len()
        && 0 <= j < addrs.len()
        && addrs[i]@ == addrs[j]@
        implies i == j by {
        if i != j {
            assert(iaddr_views(addrs)[i].au
                != iaddr_views(addrs)[j].au);
            assert(iaddr_views(addrs)[i] == addrs[i]@);
            assert(iaddr_views(addrs)[j] == addrs[j]@);
        }
    }
}

pub proof fn path_suffix_facts(
    path: LoadedBetreePath,
    start: int,
)
    requires
        path.wf(),
        0 <= start < path.lines.len(),
    ensures
        path_suffix(path, start).wf(),
        path_suffix(path, start).lines.len()
            == path.lines.len() - start,
        path_suffix(path, start).depth()
            == (path.depth() - start) as nat,
        path_suffix(path, start).lines[0] == path.lines[start],
        start == 0 ==> path_suffix(path, start) == path,
        start + 1 < path.lines.len() ==>
            path_suffix(path, start).tail()
                == path_suffix(path, start + 1),
{
    let suffix = path_suffix(path, start);
    assert(suffix.lines.len() == path.lines.len() - start);
    assert(suffix.lines[0] == path.lines[start]);
    assert forall |i: int| 0 <= i < suffix.lines.len()
        implies (#[trigger] suffix.lines[i]).wf() by {
        assert(suffix.lines[i] == path.lines[start + i]);
    }
    assert forall |i: int| 0 <= i < suffix.lines.len()
        implies (#[trigger] suffix.lines[i]).node.key_in_domain(path.key) by {
        assert(suffix.lines[i] == path.lines[start + i]);
    }
    assert forall |i: int| 0 <= i < suffix.lines.len() - 1
        implies (#[trigger] suffix.lines[i]).node.is_index() by {
        assert(suffix.lines[i] == path.lines[start + i]);
    }
    assert forall |i: int| 0 <= i < suffix.lines.len() - 1
        implies (#[trigger] suffix.lines[i]).node
            .child_ptr(suffix.key) is Some by {
        assert(suffix.lines[i] == path.lines[start + i]);
        assert(suffix.lines[i + 1] == path.lines[start + i + 1]);
        assert(path.lines[start + i].node.child_ptr(path.key) is Some);
        assert(suffix.lines[i].node.child_ptr(suffix.key)
            == path.lines[start + i].node.child_ptr(path.key));
        assert(suffix.lines[i].node.child_ptr(suffix.key) is Some);
    }
    assert forall |i: int| 0 <= i < suffix.lines.len() - 1
        implies (#[trigger] suffix.lines[i]).node
            .child_ptr(suffix.key).unwrap()
                == suffix.lines[i + 1].addr by {
        assert(suffix.lines[i] == path.lines[start + i]);
        assert(suffix.lines[i + 1] == path.lines[start + i + 1]);
        assert(path.lines[start + i].node.child_ptr(path.key).unwrap()
            == path.lines[start + i + 1].addr);
    }
    assert(suffix.wf());
    if start == 0 {
        assert(path.lines.skip(0) == path.lines);
    }
    if start + 1 < path.lines.len() {
        assert_seqs_equal!(
            path_suffix(path, start).tail().lines,
            path_suffix(path, start + 1).lines,
            i => {}
        );
    }
}

pub open spec fn ancestor_writes(
    path: LoadedBetreePath,
    new_subtree_root: Address,
    path_addrs: PathAddrs,
) -> LoadedBetree
    recommends path.lines.len() > 0, path_addrs.len() == path.depth()
    decreases path.lines.len() when path.lines.len() > 0
{
    if path.depth() == 0 {
        Map::empty()
    } else {
        let tail = path.tail();
        let tail_addrs = path_addrs.skip(1);
        let child_root = replacement_root(
            tail,
            new_subtree_root,
            tail_addrs,
        );
        let child_idx = path.lines[0].node.pivots.route(path.key);
        let new_node = crate::betree::LinkedBetree_v::BetreeNode {
            children: path.lines[0].node.children.update(
                child_idx,
                Some(child_root),
            ),
            ..path.lines[0].node
        };
        ancestor_writes(tail, new_subtree_root, tail_addrs)
            .insert(path_addrs[0], new_node)
    }
}

pub proof fn ancestor_writes_dom(
    path: LoadedBetreePath,
    new_subtree_root: Address,
    path_addrs: PathAddrs,
)
    requires
        path.lines.len() > 0,
        path_addrs.len() == path.depth(),
    ensures
        ancestor_writes(path, new_subtree_root, path_addrs).dom()
            == path_addrs.to_set(),
    decreases path.depth(),
{
    if path.depth() == 0 {
        assert(path_addrs == Seq::<Address>::empty());
    } else {
        let tail = path.tail();
        let tail_addrs = path_addrs.skip(1);
        ancestor_writes_dom(tail, new_subtree_root, tail_addrs);
        assert(path_addrs == seq![path_addrs[0]] + tail_addrs);
        crate::betree::Utils_v::lemma_to_set_distributes_over_plus(
            seq![path_addrs[0]],
            tail_addrs,
        );
        assert(path_addrs.to_set()
            == set![path_addrs[0]] + tail_addrs.to_set());
    }
}

pub proof fn substitute_writes_is_base_plus_ancestors(
    path: LoadedBetreePath,
    new_subtree_root: Address,
    base: LoadedBetree,
    path_addrs: PathAddrs,
)
    requires
        path.lines.len() > 0,
        path_addrs.len() == path.depth(),
        base.dom().disjoint(path_addrs.to_set()),
    ensures
        substitute_writes(path, new_subtree_root, base, path_addrs)
            == base.union_prefer_right(ancestor_writes(
                path,
                new_subtree_root,
                path_addrs,
            )),
    decreases path.depth(),
{
    if path.depth() == 0 {
        assert(path_addrs == Seq::<Address>::empty());
        assert(ancestor_writes(path, new_subtree_root, path_addrs).is_empty());
    } else {
        let tail = path.tail();
        let tail_addrs = path_addrs.skip(1);
        assert(path_addrs == seq![path_addrs[0]] + tail_addrs);
        crate::betree::Utils_v::lemma_to_set_distributes_over_plus(
            seq![path_addrs[0]],
            tail_addrs,
        );
        assert(base.dom().disjoint(tail_addrs.to_set()));
        substitute_writes_is_base_plus_ancestors(
            tail,
            new_subtree_root,
            base,
            tail_addrs,
        );
        assert_maps_equal!(
            substitute_writes(path, new_subtree_root, base, path_addrs),
            base.union_prefer_right(ancestor_writes(
                path,
                new_subtree_root,
                path_addrs,
            )),
            addr => {}
        );
    }
}

proof fn three_write_entries(
    left: BetreeWriteEntry,
    right: BetreeWriteEntry,
    parent: BetreeWriteEntry,
)
    requires
        left.wf(),
        right.wf(),
        parent.wf(),
        left.addr@ != right.addr@,
        left.addr@ != parent.addr@,
        right.addr@ != parent.addr@,
    ensures
        betree_write_entries_wf(seq![left, right, parent]),
        betree_node_writes(seq![left, right, parent]) == map![
            left.addr@ => raw_page_to_betree_node(left.page@),
            right.addr@ => raw_page_to_betree_node(right.page@),
            parent.addr@ => raw_page_to_betree_node(parent.page@),
        ],
{
    reveal_with_fuel(betree_node_writes, 4);

    let empty = Seq::<BetreeWriteEntry>::empty();
    assert(betree_write_entries_wf(empty));
    assert(!betree_raw_writes(empty).dom().contains(left.addr@));
    betree_write_entries_push(empty, left);
    let one = empty.push(left);
    betree_raw_writes_dom(one);
    assert(!betree_raw_writes(one).dom().contains(right.addr@));
    betree_write_entries_push(one, right);
    let two = one.push(right);
    betree_raw_writes_dom(two);
    assert(!betree_raw_writes(two).dom().contains(parent.addr@));
    betree_write_entries_push(two, parent);
    assert(seq![left, right, parent] == two.push(parent));
    assert(betree_node_writes(seq![left, right, parent])
        == betree_node_writes(seq![left, right]).insert(
            parent.addr@,
            raw_page_to_betree_node(parent.page@),
        ));
    assert(betree_node_writes(seq![left, right])
        == betree_node_writes(seq![left]).insert(
            right.addr@,
            raw_page_to_betree_node(right.page@),
        ));
    assert(betree_node_writes(seq![left])
        == Map::empty().insert(
            left.addr@,
            raw_page_to_betree_node(left.page@),
        ));
    assert_maps_equal!(
        betree_node_writes(seq![left, right, parent]),
        map![
            left.addr@ => raw_page_to_betree_node(left.page@),
            right.addr@ => raw_page_to_betree_node(right.page@),
            parent.addr@ => raw_page_to_betree_node(parent.page@),
        ],
        addr => {}
    );
}

pub proof fn path_valid_after_child_read(
    cache: Cache::State,
    path: LoadedBetreePath,
    path_reads: Map<Address, RawPage>,
    child_addr: Address,
    child_raw: RawPage,
)
    requires
        path.valid_for(Some(path.root), to_betree_nodes(path_reads)),
        forall |addr: Address| #[trigger] path_reads.contains_key(addr)
            ==> cache.valid_read(addr, path_reads[addr]),
        cache.valid_read(child_addr, child_raw),
    ensures
        path.valid_for(
            Some(path.root),
            to_betree_nodes(path_reads.insert(child_addr, child_raw)),
        ),
{
    let reads = path_reads.insert(child_addr, child_raw);
    assert(path.needed_addrs() <= to_betree_nodes(reads).dom()) by {
        assert(path.needed_addrs() <= to_betree_nodes(path_reads).dom());
    }
    assert forall |i: int| 0 <= i < path.lines.len()
        implies {
            &&& to_betree_nodes(reads).contains_key(
                (#[trigger] path.lines[i]).addr,
            )
            &&& to_betree_nodes(reads)[path.lines[i].addr]
                == path.lines[i].node
        } by {
        let addr = path.lines[i].addr;
        assert(to_betree_nodes(path_reads).contains_key(addr));
        assert(to_betree_nodes(path_reads)[addr] == path.lines[i].node);
        assert(path_reads.contains_key(addr));
        if addr == child_addr {
            Cache::State::valid_read_unique(
                cache,
                addr,
                path_reads[addr],
                child_raw,
            );
            assert(reads[addr] == child_raw);
            assert(raw_page_to_betree_node(child_raw)
                == path.lines[i].node);
        } else {
            assert(reads[addr] == path_reads[addr]);
            assert(raw_page_to_betree_node(path_reads[addr])
                == path.lines[i].node);
        }
    }
}

pub struct SplitWriteBuild {
    pub entries: Vec<BetreeWriteEntry>,
    pub new_root: IAddress,
}

pub struct AncestorWriteBuild {
    pub entries: Vec<BetreeWriteEntry>,
    pub new_root: IAddress,
}

pub fn complete_ancestor_write_batch(
    path: &BetreePathWorkspace,
    entries: Vec<BetreeWriteEntry>,
    base_root: IAddress,
    base: Ghost<LoadedBetree>,
    path_addrs: &Vec<IAddress>,
) -> (out: Option<AncestorWriteBuild>)
    requires
        path.wf(),
        path_addrs@.len() == path.receipt@.depth(),
        betree_write_entries_wf(entries@),
        to_betree_nodes(betree_raw_writes(entries@)) == base@,
        base_root@.wf(),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> (#[trigger] path_addrs@[i])@.wf(),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> betree_node_addr((#[trigger] path_addrs@[i])@),
        iaddr_views_unique(path_addrs@),
        base@.dom().disjoint(iaddr_views(path_addrs@).to_set()),
    ensures
        out is Some ==> {
            let built = out.unwrap();
            &&& betree_write_entries_wf(built.entries@)
            &&& to_betree_nodes(betree_raw_writes(built.entries@))
                == substitute_writes(
                    path.receipt@,
                    base_root@,
                    base@,
                    iaddr_views(path_addrs@),
                )
            &&& betree_raw_writes(built.entries@).dom()
                <= base@.dom() + iaddr_views(path_addrs@).to_set()
            &&& built.new_root@ == replacement_root(
                path.receipt@,
                base_root@,
                iaddr_views(path_addrs@),
            )
        },
{
    let mut entries = entries;
    let mut current = path_addrs.len();
    let mut child_root = base_root;
    proof {
        betree_path_receipt_wf(path);
        path_suffix_facts(path.receipt@, current as int);
        assert(path_suffix(path.receipt@, current as int).depth() == 0);
        assert(iaddr_views(path_addrs@).skip(current as int).len() == 0);
        assert(iaddr_views(path_addrs@).skip(current as int)
            == Seq::<Address>::empty());
        ancestor_writes_dom(
            path_suffix(path.receipt@, current as int),
            base_root@,
            iaddr_views(path_addrs@).skip(current as int),
        );
        betree_raw_writes_to_nodes(entries@);
        assert(betree_node_writes(entries@) == base@);
    }
    while current > 0
        invariant
            path.wf(),
            path.receipt@.wf(),
            path_addrs@.len() == path.receipt@.depth(),
            0 <= current <= path_addrs.len(),
            iaddr_views_unique(path_addrs@),
            base@.dom().disjoint(iaddr_views(path_addrs@).to_set()),
            child_root@ == replacement_root(
                path_suffix(path.receipt@, current as int),
                base_root@,
                iaddr_views(path_addrs@).skip(current as int),
            ),
            betree_node_writes(entries@)
                == base@.union_prefer_right(ancestor_writes(
                    path_suffix(path.receipt@, current as int),
                    base_root@,
                    iaddr_views(path_addrs@).skip(current as int),
                )),
            betree_write_entries_wf(entries@),
        decreases current,
    {
        let next = current - 1;
        let source = &path.nodes[next];
        let dest = path_addrs[next];
        proof {
            path_suffix_facts(path.receipt@, next as int);
            path_suffix_facts(path.receipt@, current as int);
            assert(path.receipt@.lines[next as int].node == source@);
            assert(path.receipt@.lines[next as int].node.key_in_domain(path.key));
            assert(source@.key_in_domain(path.key));
        }
        let replacement = match build_ancestor_replacement(
            source,
            path.key,
            child_root,
        ) {
            Some(node) => node,
            None => return None,
        };
        let page = marshall_betree_node_page(&replacement);
        let ghost entries_pre = entries@;
        let ghost old_child_root = child_root@;
        let ghost entry = BetreeWriteEntry { addr: dest, page };
        proof {
            ancestor_writes_dom(
                path_suffix(path.receipt@, current as int),
                base_root@,
                iaddr_views(path_addrs@).skip(current as int),
            );
            unique_iaddr_before_suffix(
                path_addrs@,
                next as int,
                current as int,
            );
            assert(!base@.dom().contains(dest@)) by {
                assert(iaddr_views(path_addrs@)[next as int] == dest@);
                assert(iaddr_views(path_addrs@).to_set().contains(dest@));
            }
            assert(!ancestor_writes(
                path_suffix(path.receipt@, current as int),
                base_root@,
                iaddr_views(path_addrs@).skip(current as int),
            ).dom().contains(dest@));
            betree_raw_writes_to_nodes(entries_pre);
            assert(!betree_node_writes(entries_pre).dom().contains(dest@));
            assert(!betree_raw_writes(entries_pre).dom().contains(dest@));
            assert(entry.wf());
            betree_write_entries_push(entries_pre, entry);
        }
        entries.push(BetreeWriteEntry { addr: dest, page });
        child_root = dest;
        proof {
            assert(path_suffix(path.receipt@, next as int).tail()
                == path_suffix(path.receipt@, current as int));
            assert(iaddr_views(path_addrs@).skip(next as int).skip(1)
                == iaddr_views(path_addrs@).skip(current as int));
            assert(path_suffix(path.receipt@, next as int).lines[0].node
                == source@);
            assert(entries@ == entries_pre.push(entry));
            assert(raw_page_to_betree_node(entry.page@) == replacement@);
            betree_node_writes_push(entries_pre, entry);
            assert(betree_node_writes(entries@)
                == betree_node_writes(entries_pre).insert(
                    dest@,
                    replacement@,
                ));
            let ghost old_ancestors = ancestor_writes(
                path_suffix(path.receipt@, current as int),
                base_root@,
                iaddr_views(path_addrs@).skip(current as int),
            );
            let ghost new_ancestors = ancestor_writes(
                path_suffix(path.receipt@, next as int),
                base_root@,
                iaddr_views(path_addrs@).skip(next as int),
            );
            assert(old_child_root == replacement_root(
                path_suffix(path.receipt@, current as int),
                base_root@,
                iaddr_views(path_addrs@).skip(current as int),
            ));
            assert(replacement@ == crate::betree::LinkedBetree_v::BetreeNode {
                children: source@.children.update(
                    source@.pivots.route(path.key),
                    Some(old_child_root),
                ),
                ..source@
            });
            assert(new_ancestors
                == old_ancestors.insert(dest@, replacement@));
            assert(betree_node_writes(entries@)
                == base@.union_prefer_right(new_ancestors)) by {
                assert_maps_equal!(
                    betree_node_writes(entries@),
                    base@.union_prefer_right(new_ancestors),
                    addr => {}
                );
            }
            assert(betree_write_entries_wf(entries@));
        }
        current = next;
    }
    let new_root = child_root;
    proof {
        path_suffix_facts(path.receipt@, 0);
        assert(iaddr_views(path_addrs@).skip(0) == iaddr_views(path_addrs@));
        substitute_writes_is_base_plus_ancestors(
            path.receipt@,
            base_root@,
            base@,
            iaddr_views(path_addrs@),
        );
        crate::implementation::CachedBranchBetree_v::
            substitute_writes_dom_subset(
                path.receipt@,
                base_root@,
                base@,
                iaddr_views(path_addrs@),
            );
        betree_raw_writes_to_nodes(entries@);
        assert(to_betree_nodes(betree_raw_writes(entries@))
            == substitute_writes(
                path.receipt@,
                base_root@,
                base@,
                iaddr_views(path_addrs@),
            ));
        assert(betree_raw_writes(entries@).dom()
            == to_betree_nodes(betree_raw_writes(entries@)).dom());
        assert(betree_raw_writes(entries@).dom()
            <= base@.dom() + iaddr_views(path_addrs@).to_set());
    }
    Some(AncestorWriteBuild { entries, new_root })
}

pub fn build_split_write_batch(
    path: &BetreePathWorkspace,
    child_addr: IAddress,
    child: &crate::implementation::IBetreeNode_v::IBetreeNode,
    request: &IBetreeSplitRequest,
    left_addr: IAddress,
    right_addr: IAddress,
    parent_addr: IAddress,
    path_addrs: &Vec<IAddress>,
) -> (out: Option<SplitWriteBuild>)
    requires
        path.wf(),
        path_addrs@.len() == path.receipt@.depth(),
        request.i().get_child_idx()
            < path.receipt@.target().node.children.len(),
        path.receipt@.target().node.children[
            request.i().get_child_idx() as int
        ] == Some(child_addr@),
        child.wf(),
        match request.i() {
            SplitRequest::SplitLeaf { split_key, .. } => {
                child@.can_split_leaf(split_key)
            },
            SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                child@.can_split_index(child_pivot_idx)
            },
        },
        split_parent_view(
            path.receipt@.target().node,
            child@,
            request.i(),
            left_addr@,
            right_addr@,
        ).wf(),
        left_addr@.wf(),
        right_addr@.wf(),
        parent_addr@.wf(),
        betree_node_addr(left_addr@),
        betree_node_addr(right_addr@),
        betree_node_addr(parent_addr@),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> (#[trigger] path_addrs@[i])@.wf(),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> betree_node_addr((#[trigger] path_addrs@[i])@),
        left_addr != right_addr,
        left_addr != parent_addr,
        right_addr != parent_addr,
        iaddr_views_unique(path_addrs@),
        iaddr_views(path_addrs@).to_set().disjoint(
            set![left_addr@, right_addr@, parent_addr@],
        ),
    ensures
        out is Some ==> {
            let built = out.unwrap();
            let reads = map![child_addr@ => child@];
            let new_addrs = SplitAddrs {
                left: left_addr@,
                right: right_addr@,
                parent: parent_addr@,
            };
            let model_writes = substitute_writes(
                path.receipt@,
                parent_addr@,
                split_replacement(path.receipt@, reads, request.i(), new_addrs),
                iaddr_views(path_addrs@),
            );
            &&& betree_write_entries_wf(built.entries@)
            &&& to_betree_nodes(betree_raw_writes(built.entries@))
                == model_writes
            &&& betree_raw_writes(built.entries@).dom()
                <= set![left_addr@, right_addr@, parent_addr@]
                    + iaddr_views(path_addrs@).to_set()
            &&& built.new_root@ == replacement_root(
                path.receipt@,
                parent_addr@,
                iaddr_views(path_addrs@),
            )
        },
{
    let target_idx = path.nodes.len() - 1;
    let parent = &path.nodes[target_idx];
    let pages = match build_split_node_pages(
        parent,
        child,
        request,
        left_addr,
        right_addr,
    ) {
        Some(pages) => pages,
        None => return None,
    };
    let left_page = marshall_betree_node_page(&pages.left);
    let right_page = marshall_betree_node_page(&pages.right);
    let parent_page = marshall_betree_node_page(&pages.parent);
    let mut entries = Vec::<BetreeWriteEntry>::new();
    entries.push(BetreeWriteEntry { addr: left_addr, page: left_page });
    entries.push(BetreeWriteEntry { addr: right_addr, page: right_page });
    entries.push(BetreeWriteEntry { addr: parent_addr, page: parent_page });
    let ghost split_reads = map![child_addr@ => child@];
    let ghost new_addrs = SplitAddrs {
        left: left_addr@,
        right: right_addr@,
        parent: parent_addr@,
    };
    let ghost base = split_replacement(
        path.receipt@,
        split_reads,
        request.i(),
        new_addrs,
    );
    proof {
        assert(entries@.len() == 3);
        assert(entries@[0].addr == left_addr);
        assert(entries@[1].addr == right_addr);
        assert(entries@[2].addr == parent_addr);
        assert(entries@[0].wf());
        assert(entries@[1].wf());
        assert(entries@[2].wf());
        three_write_entries(entries@[0], entries@[1], entries@[2]);
        assert(entries@ == seq![entries@[0], entries@[1], entries@[2]]);
        assert(betree_write_entries_wf(entries@));
        assert(raw_page_to_betree_node(entries@[0].page@) == pages.left@);
        assert(raw_page_to_betree_node(entries@[1].page@) == pages.right@);
        assert(raw_page_to_betree_node(entries@[2].page@) == pages.parent@);
        assert(base == map![
            left_addr@ => pages.left@,
            right_addr@ => pages.right@,
            parent_addr@ => pages.parent@,
        ]);
        assert(betree_node_writes(entries@) == base);
        betree_raw_writes_to_nodes(entries@);
    }

    let mut current = path_addrs.len();
    let mut child_root = parent_addr;
    proof {
        betree_path_receipt_wf(path);
        path_suffix_facts(path.receipt@, current as int);
        assert(path_suffix(path.receipt@, current as int).depth() == 0);
        assert(iaddr_views(path_addrs@).skip(current as int).len() == 0);
        assert(iaddr_views(path_addrs@).skip(current as int)
            == Seq::<Address>::empty());
        ancestor_writes_dom(
            path_suffix(path.receipt@, current as int),
            parent_addr@,
            iaddr_views(path_addrs@).skip(current as int),
        );
    }
    while current > 0
        invariant
            path.wf(),
            path.receipt@.wf(),
            path_addrs@.len() == path.receipt@.depth(),
            0 <= current <= path_addrs.len(),
            iaddr_views_unique(path_addrs@),
            iaddr_views(path_addrs@).to_set().disjoint(
                set![left_addr@, right_addr@, parent_addr@],
            ),
            child_root@ == replacement_root(
                path_suffix(path.receipt@, current as int),
                parent_addr@,
                iaddr_views(path_addrs@).skip(current as int),
            ),
            betree_node_writes(entries@)
                == base.union_prefer_right(ancestor_writes(
                    path_suffix(path.receipt@, current as int),
                    parent_addr@,
                    iaddr_views(path_addrs@).skip(current as int),
                )),
            betree_write_entries_wf(entries@),
        decreases current,
    {
        let next = current - 1;
        let source = &path.nodes[next];
        let dest = path_addrs[next];
        proof {
            path_suffix_facts(path.receipt@, next as int);
            path_suffix_facts(path.receipt@, current as int);
            assert(path.receipt@.lines[next as int].node == source@);
            assert(path.receipt@.lines[next as int].node.key_in_domain(path.key));
            assert(source@.key_in_domain(path.key));
        }
        let replacement = match build_ancestor_replacement(
            source,
            path.key,
            child_root,
        ) {
            Some(node) => node,
            None => return None,
        };
        let page = marshall_betree_node_page(&replacement);
        let ghost entries_pre = entries@;
        let ghost old_child_root = child_root@;
        let ghost entry = BetreeWriteEntry { addr: dest, page };
        proof {
            ancestor_writes_dom(
                path_suffix(path.receipt@, current as int),
                parent_addr@,
                iaddr_views(path_addrs@).skip(current as int),
            );
            unique_iaddr_before_suffix(
                path_addrs@,
                next as int,
                current as int,
            );
            assert(!base.dom().contains(dest@)) by {
                assert(iaddr_views(path_addrs@)[next as int] == dest@);
                assert(iaddr_views(path_addrs@).to_set()
                    .contains(dest@));
            }
            assert(!ancestor_writes(
                path_suffix(path.receipt@, current as int),
                parent_addr@,
                iaddr_views(path_addrs@).skip(current as int),
            ).dom().contains(dest@));
            betree_raw_writes_to_nodes(entries_pre);
            assert(!betree_node_writes(entries_pre).dom()
                .contains(dest@));
            assert(!betree_raw_writes(entries_pre).dom()
                .contains(dest@));
            assert(entry.wf());
            betree_write_entries_push(entries_pre, entry);
        }
        entries.push(BetreeWriteEntry { addr: dest, page });
        child_root = dest;
        proof {
            assert(path_suffix(path.receipt@, next as int).tail()
                == path_suffix(path.receipt@, current as int));
            assert(iaddr_views(path_addrs@).skip(next as int).skip(1)
                == iaddr_views(path_addrs@).skip(current as int));
            assert(path_suffix(path.receipt@, next as int).lines[0].node
                == source@);
            assert(entries@ == entries_pre.push(entry));
            assert(raw_page_to_betree_node(entry.page@) == replacement@);
            betree_node_writes_push(entries_pre, entry);
            assert(betree_node_writes(entries@)
                == betree_node_writes(entries_pre).insert(
                    dest@,
                    replacement@,
                ));
            let ghost old_ancestors = ancestor_writes(
                path_suffix(path.receipt@, current as int),
                parent_addr@,
                iaddr_views(path_addrs@).skip(current as int),
            );
            let ghost new_ancestors = ancestor_writes(
                path_suffix(path.receipt@, next as int),
                parent_addr@,
                iaddr_views(path_addrs@).skip(next as int),
            );
            assert(old_child_root == replacement_root(
                path_suffix(path.receipt@, current as int),
                parent_addr@,
                iaddr_views(path_addrs@).skip(current as int),
            ));
            assert(replacement@ == crate::betree::LinkedBetree_v::BetreeNode {
                children: source@.children.update(
                    source@.pivots.route(path.key),
                    Some(old_child_root),
                ),
                ..source@
            });
            assert(new_ancestors
                == old_ancestors.insert(dest@, replacement@));
            assert(betree_node_writes(entries@)
                == base.union_prefer_right(new_ancestors)) by {
                assert_maps_equal!(
                    betree_node_writes(entries@),
                    base.union_prefer_right(new_ancestors),
                    addr => {}
                );
            }
            assert(betree_write_entries_wf(entries@));
        }
        current = next;
    }
    let new_root = child_root;
    proof {
        path_suffix_facts(path.receipt@, 0);
        assert(iaddr_views(path_addrs@).skip(0) == iaddr_views(path_addrs@));
        substitute_writes_is_base_plus_ancestors(
            path.receipt@,
            parent_addr@,
            base,
            iaddr_views(path_addrs@),
        );
        crate::implementation::CachedBranchBetree_v::
            substitute_writes_dom_subset(
                path.receipt@,
                parent_addr@,
                base,
                iaddr_views(path_addrs@),
            );
        assert(base.dom()
            == set![left_addr@, right_addr@, parent_addr@]);
        betree_raw_writes_to_nodes(entries@);
        assert(to_betree_nodes(betree_raw_writes(entries@))
            == substitute_writes(
                path.receipt@,
                parent_addr@,
                base,
                iaddr_views(path_addrs@),
            ));
        assert(betree_raw_writes(entries@).dom()
            == to_betree_nodes(betree_raw_writes(entries@)).dom());
        assert(betree_raw_writes(entries@).dom()
            <= set![left_addr@, right_addr@, parent_addr@]
                + iaddr_views(path_addrs@).to_set());
    }
    Some(SplitWriteBuild { entries, new_root })
}

} // verus!
