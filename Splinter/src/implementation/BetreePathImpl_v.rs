// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_seqs_equal;

use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::BetreeQueryImpl_v::{
    betree_partial_path_wf, betree_path_extend_line,
    betree_path_lines_wf, betree_route_index,
    extend_betree_read_preserves,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranchBetree_v::{
    LoadedBetreePath, LoadedBetreePathLine,
};
use crate::implementation::CachingDiskBranchBetree_v::to_betree_nodes;
use crate::implementation::BetreeQueryImpl_v::cached_betree_query_valid;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle,
};
use crate::implementation::IBetreeNode_v::IBetreeNode;
use crate::marshalling::IBetreeNodeFormat_v::{
    BetreeNodePageFmt, raw_page_to_betree_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::{Element, Key, to_element};

verus! {

pub open spec fn cached_betree_path_valid(
    cache: Cache::State,
    current: Address,
    key: Key,
    fuel: nat,
    betree_aus: Set<AU>,
) -> bool
    decreases fuel,
{
    fuel > 0
    && current.wf()
    && betree_aus.contains(current.au)
    && forall |raw: RawPage| #[trigger] cache.valid_read(current, raw) ==> {
        let node = raw_page_to_betree_node(raw);
        &&& node.key_in_domain(key)
        &&& match node.child_ptr(key) {
            Some(child) => {
                &&& node.is_index()
                &&& cached_betree_path_valid(
                    cache,
                    child,
                    key,
                    (fuel - 1) as nat,
                    betree_aus,
                )
            },
            None => true,
        }
    }
}

pub open spec fn cached_betree_path_prefix_valid(
    cache: Cache::State,
    current: Address,
    key: Key,
    fuel: nat,
    depth: nat,
    betree_aus: Set<AU>,
)-> bool
    decreases depth,
{
    &&& depth < fuel
    &&& betree_aus.contains(current.au)
    &&& forall |raw: RawPage| #[trigger] cache.valid_read(current, raw) ==> {
        let node = raw_page_to_betree_node(raw);
        &&& node.key_in_domain(key)
        &&& (depth == 0 || match node.child_ptr(key) {
            Some(child) => {
                cached_betree_path_prefix_valid(
                    cache,
                    child,
                    key,
                    (fuel - 1) as nat,
                    (depth - 1) as nat,
                    betree_aus,
                )
            },
            None => true,
        })
    }
}

pub proof fn query_valid_implies_path_prefix_valid(
    cache: Cache::State,
    current: Address,
    key: Key,
    fuel: nat,
    depth: nat,
    branch_fuel: nat,
    betree_aus: Set<AU>,
    branch_summary: Map<AU, crate::allocation_layer::BranchTypes_v::Summary>,
    branch_aus: Set<AU>,
)
    requires
        depth < fuel,
        cached_betree_query_valid(
            cache,
            current,
            key,
            fuel,
            branch_fuel,
            betree_aus,
            branch_summary,
            branch_aus,
        ),
    ensures
        cached_betree_path_prefix_valid(
            cache,
            current,
            key,
            fuel,
            depth,
            betree_aus,
        ),
    decreases depth,
{
    assert forall |raw: RawPage|
        #[trigger] cache.valid_read(current, raw)
        implies {
            let node = raw_page_to_betree_node(raw);
            &&& node.key_in_domain(key)
            &&& (depth == 0 || match node.child_ptr(key) {
                Some(child) => {
                    cached_betree_path_prefix_valid(
                        cache,
                        child,
                        key,
                        (fuel - 1) as nat,
                        (depth - 1) as nat,
                        betree_aus,
                    )
                },
                None => true,
            })
        } by {
        let node = raw_page_to_betree_node(raw);
        if depth > 0 {
            match node.child_ptr(key) {
                Some(child) => {
                    query_valid_implies_path_prefix_valid(
                        cache,
                        child,
                        key,
                        (fuel - 1) as nat,
                        (depth - 1) as nat,
                        branch_fuel,
                        betree_aus,
                        branch_summary,
                        branch_aus,
                    );
                },
                None => { },
            }
        }
    }
}

pub struct BetreePathWorkspace {
    pub key: Key,
    pub root: IAddress,
    pub addrs: Vec<IAddress>,
    pub nodes: Vec<IBetreeNode>,
    pub receipt: Ghost<LoadedBetreePath>,
}

pub open spec fn path_lines(
    addrs: Seq<IAddress>,
    nodes: Seq<IBetreeNode>,
) -> Seq<LoadedBetreePathLine>
    recommends addrs.len() == nodes.len(),
{
    Seq::new(addrs.len(), |i: int| LoadedBetreePathLine {
        addr: addrs[i]@,
        node: nodes[i]@,
    })
}

pub open spec fn betree_path_addrs_wf(
    lines: Seq<LoadedBetreePathLine>,
) -> bool {
    forall |i: int| 0 <= i < lines.len()
        ==> (#[trigger] lines[i]).addr.wf()
}

proof fn pointer_equal_some(pointer: Option<Address>, addr: Address)
    requires pointer == Some(addr),
    ensures pointer is Some,
{
}

pub proof fn betree_path_receipt_wf(path: &BetreePathWorkspace)
    requires path.wf(),
    ensures path.receipt@.wf(),
{
    assert forall |i: int| 0 <= i < path.receipt@.lines.len() - 1
        implies (#[trigger] path.receipt@.lines[i]).node
            .child_ptr(path.receipt@.key) is Some by {
        assert(path.receipt@.lines[i].node.child_ptr(path.receipt@.key)
            == Some(path.receipt@.lines[i + 1].addr));
        pointer_equal_some(
            path.receipt@.lines[i].node.child_ptr(path.receipt@.key),
            path.receipt@.lines[i + 1].addr,
        );
    }
}

pub proof fn betree_path_receipt_edges(path: &BetreePathWorkspace)
    requires path.wf(),
    ensures
        forall |i: int| 0 <= i < path.receipt@.lines.len() - 1
            ==> (#[trigger] path.receipt@.lines[i]).node
                .child_ptr(path.receipt@.key)
                == Some(path.receipt@.lines[i + 1].addr),
{
}

impl BetreePathWorkspace {
    pub open spec fn wf(&self) -> bool {
        &&& self.root@.wf()
        &&& self.addrs@.len() == self.nodes@.len()
        &&& self.addrs@.len() > 0
        &&& betree_path_addrs_wf(path_lines(self.addrs@, self.nodes@))
        &&& betree_path_lines_wf(
            self.key,
            self.root@,
            path_lines(self.addrs@, self.nodes@),
        )
        &&& self.receipt@ == LoadedBetreePath {
            key: self.key,
            root: self.root@,
            lines: path_lines(self.addrs@, self.nodes@),
        }
    }
}

pub enum BetreePathLoadResult {
    Loaded {
        workspace: BetreePathWorkspace,
        reads: Ghost<Map<Address, RawPage>>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub fn load_betree_path(
    cache: &mut FracCacheImpl,
    root: IAddress,
    key: Key,
    target_depth: usize,
    fuel: usize,
    disk_page_count: crate::spec::ImplDisk_t::IPage,
    betree_aus: Ghost<Set<AU>>,
) -> (result: BetreePathLoadResult)
    requires
        old(cache).wf(),
        disk_page_count as nat == crate::disk::GenericDisk_v::page_count(),
        target_depth < fuel,
        cached_betree_path_prefix_valid(
            old(cache)@,
            root@,
            key,
            fuel as nat,
            target_depth as nat,
            betree_aus@,
        ),
    ensures
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        match result {
            BetreePathLoadResult::Loaded { workspace, reads } => {
                &&& cache@ == old(cache)@
                &&& workspace.wf()
                &&& workspace.key == key
                &&& workspace.root == root
                &&& workspace.receipt@.depth() == target_depth as nat
                &&& workspace.receipt@.valid_for(
                    Some(root@),
                    to_betree_nodes(reads@),
                )
                &&& reads@.dom() <= addresses_in_aus(betree_aus@)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    Cache::Label::Access {
                        reads: reads@,
                        writes: Map::empty(),
                    },
                )
            },
            BetreePathLoadResult::NeedCacheLoad { addr, handle } => {
                &&& betree_aus@.contains(addr@.au)
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, handle)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    crate::implementation::FracCacheImpl_v::cache_load_label(
                        &addr,
                    ),
                )
            },
            BetreePathLoadResult::CacheFull
            | BetreePathLoadResult::Blocked
            | BetreePathLoadResult::InvalidPage => {
                cache@ == old(cache)@
            },
        },
{
    let ghost cache0 = *cache;
    let ghost root_addr = root@;
    let ghost mut reads = Map::<Address, RawPage>::empty();
    let ghost mut lines = Seq::<LoadedBetreePathLine>::empty();
    let mut addrs = Vec::<IAddress>::new();
    let mut nodes = Vec::<IBetreeNode>::new();
    let mut current = root;
    let mut remaining_depth = target_depth;
    let mut remaining_fuel = fuel;

    loop
        invariant
            cache.wf(),
            cache@ == cache0@,
            cache.valid_load_handles_preserved(cache0),
            0 < remaining_fuel <= fuel,
            remaining_depth < remaining_fuel,
            remaining_depth + addrs.len() == target_depth,
            remaining_fuel + addrs.len() == fuel,
            addrs@.len() == nodes@.len(),
            addrs@.len() == lines.len(),
            lines == path_lines(addrs@, nodes@),
            betree_path_addrs_wf(lines),
            cached_betree_path_prefix_valid(
                cache0@,
                current@,
                key,
                remaining_fuel as nat,
                remaining_depth as nat,
                betree_aus@,
            ),
            betree_partial_path_wf(key, root_addr, lines, current@),
            reads.dom() == Set::new(|addr: Address| exists |i: int|
                0 <= i < lines.len() && #[trigger] lines[i].addr == addr),
            forall |i: int| 0 <= i < lines.len() ==> {
                &&& reads.contains_key((#[trigger] lines[i]).addr)
                &&& to_betree_nodes(reads)[lines[i].addr]
                    == lines[i].node
            },
            forall |addr: Address| #[trigger] reads.contains_key(addr)
                ==> cache0@.valid_read(addr, reads[addr]),
            reads.dom() <= addresses_in_aus(betree_aus@),
        decreases remaining_depth,
    {
        if current.page >= disk_page_count {
            return BetreePathLoadResult::Blocked;
        }
        proof {
            assert(current@.wf());
        }
        let ghost cache_pre_fetch = *cache;
        let handle = match cache.fetch(&current, true) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_pre_fetch,
                        *cache,
                    );
                }
                return BetreePathLoadResult::NeedCacheLoad {
                    addr: current,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::CacheFull => {
                return BetreePathLoadResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BetreePathLoadResult::Blocked;
            },
        };
        let ghost raw = handle.rec@;
        let ghost fetched_slot = handle.idx;
        let fmt = BetreeNodePageFmt::new();
        let all_slice = Slice::all(&handle.rec);
        let parsed = fmt.try_parse(&all_slice, &handle.rec);
        proof {
            assert(cache_pre_fetch@ == cache0@);
            assert(cache0@.valid_read(current@, raw));
            assert(fmt == BetreeNodePageFmt::spec_new());
            assert(all_slice@.i(handle.rec@) == raw);
        }
        let node = match parsed {
            Some(node) => {
                proof {
                    assert(node.parsedv() == fmt.parse(raw));
                    assert(raw_page_to_betree_node(raw) == node@);
                    assert(node@.key_in_domain(key));
                }
                node
            },
            None => {
                cache.handle_release(&current, handle);
                return BetreePathLoadResult::InvalidPage;
            },
        };
        cache.handle_release(&current, handle);
        proof {
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache0,
                cache_pre_fetch,
                *cache,
            );
            assert(cache@ == cache0@) by {
                assert(cache_pre_fetch@.entries
                    == cache@.entries.insert(
                        fetched_slot,
                        crate::implementation::Cache_v::Entry::Filled {
                            addr: current@,
                            data: raw,
                        },
                    ));
                assert(cache@.entries == cache_pre_fetch@.entries);
                assert(cache@.lookup_map == cache_pre_fetch@.lookup_map);
                assert(cache@.status_map == cache_pre_fetch@.status_map);
            }
        }
        let ghost node_view = node@;
        let ghost line = LoadedBetreePathLine {
            addr: current@,
            node: node_view,
        };
        let ghost reads_pre = reads;
        let ghost lines_pre = lines;
        proof {
            assert(current@.wf());
            assert(line.wf());
            betree_path_extend_line(
                key,
                root_addr,
                lines_pre,
                current@,
                line,
            );
            extend_betree_read_preserves(
                cache0@,
                reads_pre,
                lines_pre,
                current@,
                raw,
                root_addr,
                line,
            );
            reads = reads.insert(current@, raw);
            lines = lines.push(line);
            assert(betree_path_addrs_wf(lines)) by {
                assert forall |i: int| 0 <= i < lines.len()
                    implies (#[trigger] lines[i]).addr.wf() by {
                    if i == lines_pre.len() {
                        assert(lines[i] == line);
                    } else {
                        assert(lines[i] == lines_pre[i]);
                    }
                }
            }
            assert(betree_aus@.contains(current@.au));
            assert(reads.dom() <= addresses_in_aus(betree_aus@)) by {
                assert forall |addr: Address|
                    #[trigger] reads.dom().contains(addr)
                    implies addresses_in_aus(betree_aus@).contains(addr) by {
                    if addr != current@ {
                        assert(reads_pre.dom().contains(addr));
                    }
                }
            }
        }
        addrs.push(current);
        nodes.push(node);
        proof {
            assert(lines == path_lines(addrs@, nodes@)) by {
                assert_seqs_equal!(lines, path_lines(addrs@, nodes@), i => {
                    if i == lines.len() - 1 {
                        assert(lines[i] == line);
                    } else {
                        assert(lines[i] == lines_pre[i]);
                    }
                });
            }
        }
        if remaining_depth == 0 {
            let ghost receipt = LoadedBetreePath {
                key,
                root: root@,
                lines,
            };
            let workspace = BetreePathWorkspace {
                key,
                root,
                addrs,
                nodes,
                receipt: Ghost(receipt),
            };
            proof {
                assert(workspace.addrs@.len() == workspace.nodes@.len());
                assert(workspace.addrs@.len() > 0);
                assert(betree_path_lines_wf(
                    workspace.key,
                    workspace.root@,
                    path_lines(workspace.addrs@, workspace.nodes@),
                ));
                assert(betree_path_addrs_wf(
                    path_lines(workspace.addrs@, workspace.nodes@),
                ));
                assert(workspace.wf());
                assert forall |i: int|
                    0 <= i < workspace.receipt@.lines.len() - 1
                    implies (#[trigger] workspace.receipt@.lines[i]).node
                        .child_ptr(workspace.receipt@.key) is Some by {
                    assert(workspace.receipt@.lines[i].node
                        .child_ptr(workspace.receipt@.key)
                        == Some(workspace.receipt@.lines[i + 1].addr));
                    pointer_equal_some(
                        workspace.receipt@.lines[i].node
                            .child_ptr(workspace.receipt@.key),
                        workspace.receipt@.lines[i + 1].addr,
                    );
                }
                assert(workspace.receipt@.wf());
                assert(workspace.receipt@.depth() == target_depth as nat);
                assert(workspace.receipt@.valid_for(
                    Some(root_addr),
                    to_betree_nodes(reads),
                ));
                Cache::State::access_read_only_from_valid_reads(
                    cache0@,
                    reads,
                );
            }
            return BetreePathLoadResult::Loaded {
                workspace,
                reads: Ghost(reads),
            };
        }
        proof {
            assert(node_view.wf());
            assert(node_view.pivots.wf());
            Element::strictly_sorted_implies_sorted(
                node_view.pivots.pivots,
            );
        }
        let last = nodes.len() - 1;
        let last_node = &nodes[last];
        if !crate::implementation::BetreeQueryImpl_v::is_index_node(
            last_node,
        ) {
            return BetreePathLoadResult::Blocked;
        }
        let route = betree_route_index(&last_node.pivots, key);
        proof {
            assert(nodes@[last as int]@ == node_view);
            assert(node_view.is_index());
            assert(Parsedview::<Seq<Element>>::parsedv(&last_node.pivots)
                == node_view.pivots.pivots);
            assert(route as int == Element::largest_lte(
                node_view.pivots.pivots,
                to_element(key),
            ));
            assert(node_view.pivots.route(key)
                == Element::largest_lte(
                    node_view.pivots.pivots,
                    to_element(key),
                ));
            node_view.pivots.route_lemma(key);
            assert(route < last_node.children.len());
        }
        let child = match last_node.children[route] {
            Some(child) => child,
            None => return BetreePathLoadResult::Blocked,
        };
        proof {
            assert(node_view.child_ptr(key) == Some(child@));
            assert(cached_betree_path_prefix_valid(
                cache0@,
                child@,
                key,
                (remaining_fuel - 1) as nat,
                (remaining_depth - 1) as nat,
                betree_aus@,
            ));
            assert(betree_partial_path_wf(
                key,
                root_addr,
                lines,
                child@,
            ));
        }
        current = child;
        remaining_depth -= 1;
        remaining_fuel -= 1;
    }
}

} // verus!
