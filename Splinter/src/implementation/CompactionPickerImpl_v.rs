// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::BetreeQueryImpl_v::{
    betree_route_index, cached_betree_query_valid,
};
use crate::implementation::BranchBetreeImpl_v::BranchBetreeImpl;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachingDiskBranchBetree_v::to_betree_nodes;
use crate::implementation::CompactionCandidateQueueImpl_v::CompactionCandidate;
use crate::implementation::FracCacheImpl_v::{
    CACHE_SIZE_RECS, FetchErrorCode, FracCacheImpl, MutHandle,
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

pub const NORMAL_COMPACTION_BRANCH_THRESHOLD: usize = 4;
pub const TEST_COMPACTION_BRANCH_THRESHOLD: usize = 2;

#[derive(Debug, Copy, Clone)]
pub enum CompactionPickerMode {
    Root,
    TestNonRoot,
}

#[derive(Debug, Copy, Clone)]
pub enum CompactionPickerRootToken {
    Unprobed,
    Empty,
    Root { addr: IAddress },
}

pub struct CompactionPickerImpl {
    pub mode: CompactionPickerMode,
    pub observed_root: CompactionPickerRootToken,
}

pub enum CompactionPickerStepResult {
    Candidate { candidate: CompactionCandidate },
    NoCandidate,
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

enum PickerNodeReadResult {
    Loaded {
        node: IBetreeNode,
        raw: Ghost<RawPage>,
    },
    NeedCacheLoad { handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

fn read_betree_node(
    cache: &mut FracCacheImpl,
    addr: IAddress,
) -> (out: PickerNodeReadResult)
    requires old(cache).wf(),
    ensures
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        match out {
            PickerNodeReadResult::Loaded { node, raw } => {
                &&& cache@ == old(cache)@
                &&& old(cache)@.valid_read(addr@, raw@)
                &&& node@ == raw_page_to_betree_node(raw@)
                &&& BetreeNodePageFmt::spec_new().parsable(raw@)
            },
            PickerNodeReadResult::NeedCacheLoad { handle } => {
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
            PickerNodeReadResult::CacheFull
            | PickerNodeReadResult::Blocked
            | PickerNodeReadResult::InvalidPage => {
                cache@ == old(cache)@
            },
        },
{
    let ghost cache0 = *cache;
    let ghost cache_pre_fetch = *cache;
    let handle = match cache.fetch(&addr, true) {
        FetchErrorCode::Success { slot_handle } => slot_handle,
        FetchErrorCode::LoadInitiate { slot_handle } => {
            return PickerNodeReadResult::NeedCacheLoad {
                handle: slot_handle,
            };
        },
        FetchErrorCode::CacheFull => {
            return PickerNodeReadResult::CacheFull;
        },
        FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
            return PickerNodeReadResult::Blocked;
        },
    };

    let ghost raw = handle.rec@;
    let ghost fetched_slot = handle.idx;
    let fmt = BetreeNodePageFmt::new();
    let all_slice = Slice::all(&handle.rec);
    let parsed = fmt.try_parse(&all_slice, &handle.rec);
    proof {
        assert(cache_pre_fetch@ == cache0@);
        assert(cache0@.valid_read(addr@, raw));
        if parsed is Some {
            assert(fmt == BetreeNodePageFmt::spec_new());
            assert(all_slice@.i(handle.rec@) == raw);
            assert(fmt.parsable(raw));
            assert(parsed.unwrap().parsedv() == fmt.parse(raw));
            assert(raw_page_to_betree_node(raw) == parsed.unwrap()@);
        }
    }
    cache.handle_release(&addr, handle);
    proof {
        FracCacheImpl::valid_load_handles_preserved_transitive(
            cache0,
            cache_pre_fetch,
            *cache,
        );
        assert(cache_pre_fetch@.entries
            == cache@.entries.insert(
                fetched_slot,
                crate::implementation::Cache_v::Entry::Filled {
                    addr: addr@,
                    data: raw,
                },
            ));
        assert(cache@.entries == cache_pre_fetch@.entries);
        assert(cache@.lookup_map == cache_pre_fetch@.lookup_map);
        assert(cache@.status_map == cache_pre_fetch@.status_map);
        assert(cache@ == cache0@);
    }
    match parsed {
        Some(node) => PickerNodeReadResult::Loaded {
            node,
            raw: Ghost(raw),
        },
        None => PickerNodeReadResult::InvalidPage,
    }
}

impl CompactionPickerImpl {
    pub open spec fn wf(&self) -> bool {
        true
    }

    pub fn new(test_non_root: bool) -> (out: Self)
        ensures out.wf(), out.observed_root is Unprobed,
    {
        Self {
            mode: if test_non_root {
                CompactionPickerMode::TestNonRoot
            } else {
                CompactionPickerMode::Root
            },
            observed_root: CompactionPickerRootToken::Unprobed,
        }
    }

    fn same_addr(left: &IAddress, right: &IAddress) -> (out: bool)
        ensures out == (left@ == right@),
    {
        left.au == right.au && left.page == right.page
    }

    pub fn needs_probe(&self, root: &Option<IAddress>) -> (out: bool)
        ensures out == match (self.observed_root, root) {
            (CompactionPickerRootToken::Unprobed, _) => true,
            (CompactionPickerRootToken::Empty, None) => false,
            (CompactionPickerRootToken::Root { addr }, Some(root_addr)) => {
                addr@ != root_addr@
            },
            _ => true,
        },
    {
        match (self.observed_root, root) {
            (CompactionPickerRootToken::Unprobed, _) => true,
            (CompactionPickerRootToken::Empty, None) => false,
            (
                CompactionPickerRootToken::Root { addr },
                Some(root_addr),
            ) => !Self::same_addr(&addr, root_addr),
            _ => true,
        }
    }

    fn mark_observed(&mut self, root: Option<IAddress>)
        requires old(self).wf(),
        ensures self.wf(),
    {
        self.observed_root = match root {
            Some(addr) => CompactionPickerRootToken::Root { addr },
            None => CompactionPickerRootToken::Empty,
        };
    }

    pub fn step(
        &mut self,
        branch: &BranchBetreeImpl,
        cache: &mut FracCacheImpl,
    ) -> (out: CompactionPickerStepResult)
        requires
            old(self).wf(),
            branch.wf(),
            branch.control.metadata_loaded,
            old(cache).wf(),
            branch.query_cache_inv(old(cache)@),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            old(cache)@.inv() ==> cache@.inv(),
            match out {
                CompactionPickerStepResult::Candidate { candidate } => {
                    &&& candidate.wf()
                    &&& candidate.fuel == CACHE_SIZE_RECS
                    &&& candidate.start == 0
                    &&& cache@ == old(cache)@
                },
                CompactionPickerStepResult::NoCandidate
                | CompactionPickerStepResult::InvalidPage => {
                    cache@ == old(cache)@
                },
                CompactionPickerStepResult::NeedCacheLoad { addr, handle } => {
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& branch.ownership.betree.active_aus()
                        .contains(addr@.au)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                CompactionPickerStepResult::CacheFull
                | CompactionPickerStepResult::Blocked => {
                    cache@ == old(cache)@
                },
            },
    {
        let root = match branch.root {
            Some(root) => root,
            None => {
                self.mark_observed(None);
                return CompactionPickerStepResult::NoCandidate;
            },
        };
        if !self.needs_probe(&Some(root)) {
            return CompactionPickerStepResult::NoCandidate;
        }

        let key = Key(0);
        let ghost cache0 = *cache;
        let ghost betree_aus = branch.ownership.betree.active_aus();
        let ghost branch_summary =
            branch.ownership.branches.active_summary_map();
        let ghost branch_aus =
            branch.ownership.branches.active_summary_aus();
        proof {
            assert(CACHE_SIZE_RECS > 1);
            assert(cached_betree_query_valid(
                cache0@,
                root@,
                key,
                CACHE_SIZE_RECS as nat,
                CACHE_SIZE_RECS as nat,
                betree_aus,
                branch_summary,
                branch_aus,
            ));
        }
        let root_read = read_betree_node(cache, root);
        let (root_node, root_raw) = match root_read {
            PickerNodeReadResult::Loaded { node, raw } => (node, raw),
            PickerNodeReadResult::NeedCacheLoad { handle } => {
                proof {
                    assert(betree_aus.contains(root@.au));
                    if cache0@.inv() {
                        Cache::State::inv_next(
                            cache0@,
                            cache@,
                            crate::implementation::FracCacheImpl_v::cache_load_label(
                                &root,
                            ),
                        );
                    }
                }
                return CompactionPickerStepResult::NeedCacheLoad {
                    addr: root,
                    handle,
                };
            },
            PickerNodeReadResult::CacheFull => {
                return CompactionPickerStepResult::CacheFull;
            },
            PickerNodeReadResult::Blocked => {
                return CompactionPickerStepResult::Blocked;
            },
            PickerNodeReadResult::InvalidPage => {
                self.mark_observed(Some(root));
                return CompactionPickerStepResult::InvalidPage;
            },
        };
        proof {
            assert(cache@ == cache0@);
            assert(cache0@.valid_read(root@, root_raw@));
            assert(root_node@ == raw_page_to_betree_node(root_raw@));
            assert(root_node@.key_in_domain(key));
        }

        match self.mode {
            CompactionPickerMode::Root => {
                self.mark_observed(Some(root));
                if root_node.buffers.len()
                    < NORMAL_COMPACTION_BRANCH_THRESHOLD
                {
                    return CompactionPickerStepResult::NoCandidate;
                }
                let end = root_node.buffers.len();
                CompactionPickerStepResult::Candidate {
                    candidate: CompactionCandidate {
                        route_key: key,
                        target_addr: root,
                        target_depth: 0,
                        fuel: CACHE_SIZE_RECS,
                        start: 0,
                        end,
                    },
                }
            },
            CompactionPickerMode::TestNonRoot => {
                proof {
                    assert(root_node@.wf());
                    assert(root_node@.pivots.wf());
                    Element::strictly_sorted_implies_sorted(
                        root_node@.pivots.pivots,
                    );
                }
                let route = betree_route_index(&root_node.pivots, key);
                proof {
                    assert(route as int == Element::largest_lte(
                        root_node@.pivots.pivots,
                        to_element(key),
                    ));
                    assert(root_node@.pivots.route(key)
                        == Element::largest_lte(
                            root_node@.pivots.pivots,
                            to_element(key),
                        ));
                    root_node@.pivots.route_lemma(key);
                    assert(route as int
                        == root_node@.pivots.route(key));
                    assert(route < root_node.children.len());
                }
                let child = match root_node.children[route] {
                    Some(child) => child,
                    None => {
                        self.mark_observed(Some(root));
                        return CompactionPickerStepResult::NoCandidate;
                    },
                };
                proof {
                    assert(root_node@.child_ptr(key) == Some(child@));
                    assert(cached_betree_query_valid(
                        cache0@,
                        child@,
                        key,
                        (CACHE_SIZE_RECS - 1) as nat,
                        CACHE_SIZE_RECS as nat,
                        betree_aus,
                        branch_summary,
                        branch_aus,
                    ));
                }
                let child_read = read_betree_node(cache, child);
                let (child_node, child_raw) = match child_read {
                    PickerNodeReadResult::Loaded { node, raw } => (node, raw),
                    PickerNodeReadResult::NeedCacheLoad { handle } => {
                        proof {
                            assert(betree_aus.contains(child@.au));
                            if cache0@.inv() {
                                Cache::State::inv_next(
                                    cache0@,
                                    cache@,
                                    crate::implementation::FracCacheImpl_v::cache_load_label(
                                        &child,
                                    ),
                                );
                            }
                        }
                        return CompactionPickerStepResult::NeedCacheLoad {
                            addr: child,
                            handle,
                        };
                    },
                    PickerNodeReadResult::CacheFull => {
                        return CompactionPickerStepResult::CacheFull;
                    },
                    PickerNodeReadResult::Blocked => {
                        return CompactionPickerStepResult::Blocked;
                    },
                    PickerNodeReadResult::InvalidPage => {
                        self.mark_observed(Some(root));
                        return CompactionPickerStepResult::InvalidPage;
                    },
                };
                proof {
                    assert(cache@ == cache0@);
                    assert(cache0@.valid_read(child@, child_raw@));
                    assert(child_node@
                        == raw_page_to_betree_node(child_raw@));
                    assert(child_node@.key_in_domain(key));
                }
                self.mark_observed(Some(root));
                if child_node.buffers.len()
                    < TEST_COMPACTION_BRANCH_THRESHOLD
                {
                    return CompactionPickerStepResult::NoCandidate;
                }
                let end = child_node.buffers.len();
                CompactionPickerStepResult::Candidate {
                    candidate: CompactionCandidate {
                        route_key: key,
                        target_addr: child,
                        target_depth: 1,
                        fuel: CACHE_SIZE_RECS,
                        start: 0,
                        end,
                    },
                }
            },
        }
    }
}

} // verus!
