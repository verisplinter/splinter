// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::allocation_layer::BranchTypes_v::BranchNode;
use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::CachedBranch_v::{
    LoadedPathReceipt, LoadedPathReceiptLine,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachingDiskBranchBetree_v::to_branch_nodes;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle,
};
use crate::marshalling::IBranchNodeFormat_v::{
    BranchNodePageFmt, raw_page_to_branch_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Delta, Message};

verus! {

pub enum BranchPathQueryResult {
    Loaded {
        message: Message,
        reads: Ghost<Map<Address, RawPage>>,
        receipt: Ghost<LoadedPathReceipt>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub open spec fn branch_path_line_for(
    addr: Address,
    raw: RawPage,
) -> LoadedPathReceiptLine {
    LoadedPathReceiptLine {
        addr,
        node: raw_page_to_branch_node(raw),
    }
}

// This is the cache-facing consequence of the sealed-branch invariant.  It
// permits missing pages, but every resident page on the selected path has the
// semantic shape needed to route to the next page.
pub open spec fn cached_branch_path_valid(
    cache: Cache::State,
    current: Address,
    key: Key,
    fuel: nat,
    allowed_aus: Set<AU>,
) -> bool
    decreases fuel,
{
    fuel == 0 || {
        &&& allowed_aus.contains(current.au)
        &&& forall |raw: RawPage| #[trigger] cache.valid_read(current, raw) ==> {
            let node = raw_page_to_branch_node(raw);
            let line = LoadedPathReceiptLine { addr: current, node };
            &&& line.wf()
            &&& match node {
                BranchNode::Leaf { .. } => true,
                BranchNode::Index { children, .. } => {
                    let child_idx = node.route(key) + 1;
                    &&& 0 <= child_idx < children.len()
                    &&& cached_branch_path_valid(
                        cache,
                        children[child_idx],
                        key,
                        (fuel - 1) as nat,
                        allowed_aus,
                    )
                },
                BranchNode::Auxiliary(_) => false,
            }
        }
    }
}

pub open spec fn branch_path_lines_wf(
    key: Key,
    root: Address,
    lines: Seq<LoadedPathReceiptLine>,
) -> bool {
    &&& (lines.len() == 0 || lines[0].addr == root)
    &&& forall |i: int| 0 <= i < lines.len() - 1
        ==> (#[trigger] lines[i]).node is Index
    &&& forall |i: int| 0 <= i < lines.len()
        ==> (#[trigger] lines[i]).wf()
    &&& forall |i: int| 0 <= i < lines.len() - 1 ==> {
        let line = lines[i];
        let child_idx = line.node.route(key) + 1;
        line.node->children[child_idx] == (#[trigger] lines[i + 1]).addr
    }
}

pub open spec fn branch_partial_path_wf(
    key: Key,
    root: Address,
    lines: Seq<LoadedPathReceiptLine>,
    current: Address,
) -> bool {
    &&& branch_path_lines_wf(key, root, lines)
    &&& lines.len() == 0 ==> current == root
    &&& lines.len() > 0 ==> {
        let line = lines.last();
        let child_idx = line.node.route(key) + 1;
        &&& line.node is Index
        &&& line.node->children[child_idx] == current
    }
}

fn route_index(pivots: &Vec<Key>, key: Key) -> (out: usize)
    ensures
        out <= pivots.len(),
        Key::is_sorted(pivots@)
            ==> out as int == Key::largest_lte(pivots@, key) + 1,
{
    let mut idx = 0usize;
    while idx < pivots.len() && pivots[idx].0 <= key.0
        invariant
            idx <= pivots.len(),
            forall |i: int| 0 <= i < idx
                ==> Key::lte(#[trigger] pivots@[i], key),
        decreases pivots.len() - idx,
    {
        proof { assert(Key::lte(pivots@[idx as int], key)); }
        idx += 1;
    }
    proof {
        if Key::is_sorted(pivots@) {
            let r = idx as int - 1;
            if idx < pivots.len() {
                assert(!(pivots@[idx as int].0 <= key.0));
                assert(Key::lt(key, pivots@[idx as int]));
            }
            if idx > 0 {
                assert(Key::lte(pivots@[idx as int - 1], key));
            }
            Key::largest_lte_is_lemma(pivots@, key, r);
        }
    }
    idx
}

pub open spec fn leaf_query_result(
    keys: Seq<Key>,
    msgs: Seq<Message>,
    key: Key,
) -> Message {
    let leaf = BranchNode::Leaf { keys, msgs };
    let idx = leaf.route(key);
    if 0 <= idx && leaf->keys[idx] == key {
        leaf->msgs[idx]
    } else {
        Message::Update { delta: Delta(0) }
    }
}

fn query_leaf_message(
    keys: &Vec<Key>,
    msgs: &Vec<Message>,
    key: Key,
) -> (message: Message)
    requires
        keys@.len() > 0,
        keys@.len() == msgs@.len(),
        Key::is_strictly_sorted(keys@),
    ensures message == leaf_query_result(keys@, msgs@, key),
{
    let mut idx = 0usize;
    while idx < keys.len()
        invariant
            idx <= keys.len(),
            keys@.len() > 0,
            keys@.len() == msgs@.len(),
            Key::is_strictly_sorted(keys@),
            forall |i: int| 0 <= i < idx
                ==> #[trigger] keys@[i] != key,
        decreases keys.len() - idx,
    {
        if keys[idx].0 == key.0 {
            let message = msgs[idx];
            proof {
                assert(keys@[idx as int] == key);
                let route = Key::largest_lte(keys@, key);
                Key::strictly_sorted_implies_sorted(keys@);
                Key::largest_lte_ensures(keys@, key, route);
                assert(keys@.contains(key));
                assert(0 <= route < keys@.len());
                assert(keys@[route] == key);
                Key::strictly_sorted_implies_unique(keys@);
                assert(route == idx as int);
            }
            return message;
        }
        proof { assert(keys@[idx as int] != key); }
        idx += 1;
    }
    let message = Message::Update { delta: Delta(0) };
    proof {
        assert forall |i: int| 0 <= i < keys@.len()
            implies #[trigger] keys@[i] != key by { }
        Key::strictly_sorted_implies_sorted(keys@);
        let route = Key::largest_lte(keys@, key);
        Key::largest_lte_ensures(keys@, key, route);
        if 0 <= route {
            assert(route < keys@.len());
            assert(keys@[route] != key);
        }
    }
    message
}

proof fn extend_read_preserves(
    cache: Cache::State,
    reads_pre: Map<Address, RawPage>,
    lines_pre: Seq<LoadedPathReceiptLine>,
    current: Address,
    raw: RawPage,
    root: Address,
    line: LoadedPathReceiptLine,
)
    requires
        line.addr == current,
        lines_pre.len() == 0 ==> current == root,
        lines_pre.len() > 0 ==> lines_pre[0].addr == root,
        reads_pre.dom() == Set::new(|addr: Address| exists |i: int|
            0 <= i < lines_pre.len()
                && #[trigger] lines_pre[i].addr == addr),
        forall |addr: Address| #[trigger] reads_pre.contains_key(addr)
            ==> cache.valid_read(addr, reads_pre[addr]),
        cache.valid_read(current, raw),
    ensures ({
        let reads = reads_pre.insert(current, raw);
        let lines = lines_pre.push(line);
        &&& lines.len() > 0
        &&& lines[0].addr == root
        &&& reads.dom() == Set::new(|addr: Address| exists |i: int|
            0 <= i < lines.len() && #[trigger] lines[i].addr == addr)
        &&& forall |addr: Address| #[trigger] reads.contains_key(addr)
            ==> cache.valid_read(addr, reads[addr])
    }),
{
    let reads = reads_pre.insert(current, raw);
    let lines = lines_pre.push(line);
    if lines_pre.len() == 0 {
        assert(lines[0] == line);
    } else {
        assert(lines[0] == lines_pre[0]);
    }
    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
        implies cache.valid_read(addr, reads[addr]) by {
        if addr != current {
            assert(reads_pre.contains_key(addr));
        }
    }
    assert(reads.dom() == Set::new(|addr: Address| exists |i: int|
        0 <= i < lines.len() && #[trigger] lines[i].addr == addr)) by {
        assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
            <==> (exists |i: int| 0 <= i < lines.len()
                && #[trigger] lines[i].addr == addr) by {
            if addr == current {
                assert(lines[(lines.len() - 1) as int] == line);
            } else if reads.dom().contains(addr) {
                assert(reads_pre.dom().contains(addr));
                let i = choose |i: int| 0 <= i < lines_pre.len()
                    && #[trigger] lines_pre[i].addr == addr;
                assert(lines[i] == lines_pre[i]);
            } else if exists |i: int| 0 <= i < lines.len()
                && #[trigger] lines[i].addr == addr
            {
                let i = choose |i: int| 0 <= i < lines.len()
                    && #[trigger] lines[i].addr == addr;
                if i == lines.len() - 1 {
                    assert(addr == current);
                } else {
                    assert(i < lines_pre.len());
                    assert(lines[i] == lines_pre[i]);
                    assert(reads_pre.dom().contains(addr));
                }
            }
        }
    }
}

pub fn load_branch_path(
    cache: &mut FracCacheImpl,
    root: IAddress,
    key: Key,
    max_depth: usize,
    allowed_aus: Ghost<Set<AU>>,
) -> (out: BranchPathQueryResult)
    requires
        old(cache).wf(),
        max_depth > 0,
        cached_branch_path_valid(
            old(cache)@,
            root@,
            key,
            max_depth as nat,
            allowed_aus@,
        ),
    ensures
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        forall |addr: Address, data: RawPage|
            old(cache)@.valid_read(addr, data)
            ==> cache@.valid_read(addr, data),
        forall |addr: Address, data: RawPage|
            cache@.valid_read(addr, data)
            ==> old(cache)@.valid_read(addr, data),
        match out {
            BranchPathQueryResult::Loaded { message, reads, receipt } => {
                &&& cache@ == old(cache)@
                &&& receipt@.key == key
                &&& receipt@.valid_for(root@, to_branch_nodes(reads@))
                &&& receipt@.target().node is Leaf
                &&& message == receipt@.result()
                &&& reads@.dom() <= addresses_in_aus(allowed_aus@)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    Cache::Label::Access {
                        reads: reads@,
                        writes: Map::empty(),
                    },
                )
            },
            BranchPathQueryResult::NeedCacheLoad { addr, handle } => {
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, handle)
                &&& allowed_aus@.contains(addr@.au)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                )
            },
            BranchPathQueryResult::CacheFull
            | BranchPathQueryResult::Blocked
            | BranchPathQueryResult::InvalidPage => cache@ == old(cache)@,
        },
{
    let ghost cache0 = *cache;
    let ghost root_addr = root@;
    let ghost mut reads = Map::<Address, RawPage>::empty();
    let ghost mut lines = Seq::<LoadedPathReceiptLine>::empty();
    let mut current = root;
    let mut remaining = max_depth;

    while remaining > 0
        invariant
            cache.wf(),
            cache@ == cache0@,
            cache.valid_load_handles_preserved(cache0),
            0 < remaining <= max_depth,
            cached_branch_path_valid(
                cache0@,
                current@,
                key,
                remaining as nat,
                allowed_aus@,
            ),
            branch_partial_path_wf(key, root_addr, lines, current@),
            reads.dom() == Set::new(|addr: Address| exists |i: int|
                0 <= i < lines.len() && #[trigger] lines[i].addr == addr),
            forall |i: int| 0 <= i < lines.len() ==> {
                &&& reads.contains_key((#[trigger] lines[i]).addr)
                &&& to_branch_nodes(reads)[lines[i].addr] == lines[i].node
            },
            forall |addr: Address| #[trigger] reads.contains_key(addr)
                ==> cache0@.valid_read(addr, reads[addr]),
            reads.dom() <= addresses_in_aus(allowed_aus@),
        decreases remaining,
    {
        let ghost cache_pre_fetch = *cache;
        match cache.fetch(&current, true) {
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_pre_fetch,
                        *cache,
                    );
                }
                return BranchPathQueryResult::NeedCacheLoad {
                    addr: current,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::Success { slot_handle } => {
                let ghost raw = slot_handle.rec@;
                let ghost fetched_slot = slot_handle.idx;
                let fmt = BranchNodePageFmt::new();
                let all_slice = Slice::all(&slot_handle.rec);
                let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                proof {
                    assert(cache_pre_fetch@ == cache0@);
                    assert(cache0@.valid_read(current@, raw));
                    if parsed is Some {
                        assert(fmt == BranchNodePageFmt::spec_new());
                        assert(all_slice@.i(slot_handle.rec@) == raw);
                        assert(fmt.parsable(all_slice@.i(slot_handle.rec@)));
                        assert(BranchNodePageFmt::spec_new().parsable(raw));
                        assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                        assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
                    }
                }
                cache.handle_release(&current, slot_handle);
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
                                addr: current@,
                                data: raw,
                            },
                        ));
                    assert(cache@.entries == cache_pre_fetch@.entries);
                    assert(cache@.lookup_map == cache_pre_fetch@.lookup_map);
                    assert(cache@.status_map == cache_pre_fetch@.status_map);
                    assert(cache@ == cache0@);
                }
                let node = match parsed {
                    Some(node) => node,
                    None => return BranchPathQueryResult::InvalidPage,
                };
                let ghost node_view = node@;
                let ghost line = LoadedPathReceiptLine {
                    addr: current@,
                    node: node_view,
                };
                let ghost reads_pre = reads;
                let ghost lines_pre = lines;
                proof {
                    assert(line.wf());
                    extend_read_preserves(
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
                    assert(allowed_aus@.contains(current@.au));
                    assert(reads.dom() <= addresses_in_aus(allowed_aus@)) by {
                        assert forall |addr: Address| #[trigger] reads.dom().contains(addr)
                            implies addresses_in_aus(allowed_aus@).contains(addr) by {
                            if addr == current@ {
                            } else {
                                assert(reads_pre.dom().contains(addr));
                            }
                        }
                    }
                    assert(to_branch_nodes(reads)[current@] == node_view);
                    assert forall |i: int| 0 <= i < lines.len()
                        implies {
                            &&& reads.contains_key((#[trigger] lines[i]).addr)
                            &&& to_branch_nodes(reads)[lines[i].addr]
                                == lines[i].node
                        } by {
                        if i == lines.len() - 1 {
                            assert(lines[i] == line);
                        } else {
                            assert(i < lines_pre.len());
                            assert(lines[i] == lines_pre[i]);
                            if lines[i].addr == current@ {
                                Cache::State::valid_read_unique(
                                    cache0@,
                                    current@,
                                    reads_pre[current@],
                                    raw,
                                );
                            }
                        }
                    }
                }

                match node {
                    crate::implementation::IBranchNode_v::IBranchNode::Leaf {
                        keys,
                        msgs,
                    } => {
                        let message = query_leaf_message(&keys, &msgs, key);
                        let ghost receipt = LoadedPathReceipt {
                            key,
                            root: root_addr,
                            lines,
                        };
                        proof {
                            assert(branch_path_lines_wf(key, root_addr, lines));
                            assert(receipt.wf());
                            assert(receipt.needed_addrs() == reads.dom());
                            assert forall |i: int| 0 <= i < receipt.lines.len()
                                implies {
                                    &&& to_branch_nodes(reads).contains_key(
                                        (#[trigger] receipt.lines[i]).addr,
                                    )
                                    &&& to_branch_nodes(reads)[receipt.lines[i].addr]
                                        == receipt.lines[i].node
                                } by { }
                            assert(receipt.valid_for(root_addr, to_branch_nodes(reads)));
                            assert(receipt.target() == line);
                            assert(receipt.target().node is Leaf);
                            assert(message == leaf_query_result(keys@, msgs@, key));
                            assert(message == receipt.result());
                            Cache::State::access_read_only_from_valid_reads(
                                cache0@,
                                reads,
                            );
                        }
                        return BranchPathQueryResult::Loaded {
                            message,
                            reads: Ghost(reads),
                            receipt: Ghost(receipt),
                        };
                    },
                    crate::implementation::IBranchNode_v::IBranchNode::Index {
                        pivots,
                        children,
                        aux_ptr: _,
                    } => {
                        let child_idx = route_index(&pivots, key);
                        proof {
                            assert(Key::is_strictly_sorted(pivots@));
                            Key::strictly_sorted_implies_sorted(pivots@);
                            assert(child_idx as int == node_view.route(key) + 1);
                            assert(0 <= node_view.route(key) + 1
                                < node_view->children.len());
                            assert(child_idx < children.len());
                        }
                        remaining -= 1;
                        if remaining == 0 {
                            proof { assert(cache@ == cache0@); }
                            return BranchPathQueryResult::Blocked;
                        }
                        current = children[child_idx];
                        proof {
                            assert(lines.last() == line);
                            assert(line.node->children[line.node.route(key) + 1]
                                == current@);
                            assert(branch_partial_path_wf(
                                key,
                                root_addr,
                                lines,
                                current@,
                            ));
                            assert(cached_branch_path_valid(
                                cache0@,
                                current@,
                                key,
                                remaining as nat,
                                allowed_aus@,
                            ));
                        }
                    },
                    crate::implementation::IBranchNode_v::IBranchNode::Auxiliary {
                        summary_aus: _,
                    } => {
                        proof { assert(cache@ == cache0@); }
                        return BranchPathQueryResult::InvalidPage;
                    },
                }
            },
            FetchErrorCode::CacheFull => {
                return BranchPathQueryResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BranchPathQueryResult::Blocked;
            },
        }
    }
    proof { assert(cache@ == cache0@); }
    BranchPathQueryResult::Blocked
}

} // verus!
