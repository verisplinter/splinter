// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::betree::LinkedBetree_v::BetreeNode;
use crate::allocation_layer::BranchTypes_v::Summary;
use crate::disk::GenericDisk_v::{AU, Address};
use crate::implementation::BranchPathQueryImpl_v::{
    BranchPathQueryResult, cached_branch_path_valid, load_branch_path,
};
use crate::implementation::CachedBranchBetree_v::{
    LoadedBetreePath, LoadedBetreePathLine, LoadedBetreeQueryReceipt,
    branch_receipts_result, branch_receipts_valid,
};
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachingDiskBranchBetree_v::{
    to_betree_nodes, to_branch_nodes,
};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle,
};
use crate::implementation::IBetreeNode_v::{IBetreeNode, IElement};
use crate::marshalling::IBetreeNodeFormat_v::{
    BetreeNodePageFmt, raw_page_to_betree_node,
};
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::{Element, Key, to_element};
use crate::spec::Messages_t::{Delta, Message, Value, default_value};

verus! {

pub enum BetreeQueryResult {
    Loaded {
        value: Value,
        disk_message: Message,
        betree_reads: Ghost<Map<Address, RawPage>>,
        branch_reads: Ghost<Map<Address, RawPage>>,
        receipt: Ghost<LoadedBetreeQueryReceipt>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub open spec fn cached_betree_query_valid(
    cache: Cache::State,
    current: Address,
    key: Key,
    betree_fuel: nat,
    branch_fuel: nat,
    betree_aus: Set<AU>,
    branch_summary: Map<AU, Summary>,
    branch_aus: Set<AU>,
) -> bool
    decreases betree_fuel,
{
    betree_fuel == 0 || {
        &&& branch_fuel > 0
        &&& betree_aus.contains(current.au)
        &&& forall |raw: RawPage| #[trigger] cache.valid_read(current, raw) ==> {
            let node = raw_page_to_betree_node(raw);
            &&& node.key_in_domain(key)
            &&& forall |i: int|
                node.flushed_ofs(key) <= i < node.buffers.len()
                ==> {
                    let root = #[trigger] node.buffers.addrs[i];
                    &&& branch_summary.contains_key(root.au)
                    &&& branch_summary[root.au] <= branch_aus
                    &&& cached_branch_path_valid(
                        cache,
                        root,
                        key,
                        branch_fuel,
                        branch_summary[root.au],
                    )
                }
            &&& match node.child_ptr(key) {
                Some(child) => {
                    cached_betree_query_valid(
                        cache,
                        child,
                        key,
                        (betree_fuel - 1) as nat,
                        branch_fuel,
                        betree_aus,
                        branch_summary,
                        branch_aus,
                    )
                },
                None => true,
            }
        }
    }
}

pub fn is_index_node(node: &IBetreeNode) -> (out: bool)
    ensures out == node@.is_index(),
{
    let mut index = 0usize;
    while index < node.children.len()
        invariant
            index <= node.children.len(),
            forall |i: int| 0 <= i < index
                ==> (#[trigger] node.children@[i]) is Some,
        decreases node.children.len() - index,
    {
        if node.children[index].is_none() {
            proof {
                assert(node@.valid_child_index(index as nat));
                assert(node@.children[index as int] is None);
                assert(!node@.is_index());
            }
            return false;
        }
        index += 1;
    }
    proof {
        assert forall |i: nat| #[trigger] node@.valid_child_index(i)
            implies node@.children[i as int] is Some by {
            assert(i < node.children.len());
        }
    }
    true
}

fn element_lte_key(element: &IElement, key: Key) -> (out: bool)
    ensures out == Element::lte(element@, to_element(key)),
{
    match element {
        IElement::Max => false,
        IElement::Elem { e } => *e <= key.0,
    }
}

pub fn betree_route_index(pivots: &Vec<IElement>, key: Key) -> (out: usize)
    requires
        pivots.len() > 0,
        Element::is_sorted(
            crate::marshalling::Marshalling_v::Parsedview::<
                Seq<Element>,
            >::parsedv(pivots),
        ),
        Element::lte(
            crate::marshalling::Marshalling_v::Parsedview::<
                Seq<Element>,
            >::parsedv(pivots)[0],
            to_element(key),
        ),
    ensures
        out < pivots.len(),
        out as int == Element::largest_lte(
            crate::marshalling::Marshalling_v::Parsedview::<
                Seq<Element>,
            >::parsedv(pivots),
            to_element(key),
        ),
{
    let ghost pivot_view = crate::marshalling::Marshalling_v::Parsedview::<
        Seq<Element>,
    >::parsedv(pivots);
    let mut idx = 0usize;
    while idx < pivots.len() && element_lte_key(&pivots[idx], key)
        invariant
            idx <= pivots.len(),
            pivot_view.len() == pivots.len(),
            Element::is_sorted(pivot_view),
            forall |i: int| 0 <= i < idx
                ==> Element::lte(#[trigger] pivot_view[i], to_element(key)),
        decreases pivots.len() - idx,
    {
        idx += 1;
    }
    proof {
        let route = Element::largest_lte(pivot_view, to_element(key));
        Element::largest_lte_lemma(pivot_view, to_element(key), route);
        assert(-1 <= route < pivot_view.len());
        if idx < pivots.len() {
            assert(!Element::lte(pivot_view[idx as int], to_element(key)));
            assert(Element::lt(to_element(key), pivot_view[idx as int]));
        }
        if route < idx as int - 1 {
            assert(0 <= route + 1 < idx as int);
            assert(Element::lte(pivot_view[route + 1], to_element(key)));
            assert(Element::lt(to_element(key), pivot_view[route + 1]));
            assert(false);
        }
        if route > idx as int - 1 {
            assert(idx as int <= route);
            assert(idx < pivots.len());
            assert(Element::lt(to_element(key), pivot_view[idx as int]));
            assert(Element::lte(pivot_view[idx as int], to_element(key)));
            assert(false);
        }
        assert(route == idx as int - 1);
        assert(idx > 0) by {
            if idx == 0 {
                assert(!Element::lte(pivot_view[0], to_element(key)));
            }
        }
    }
    idx - 1
}

fn combine_deltas(new_delta: Delta, old_delta: Delta) -> (out: Delta)
    ensures out == Message::combine_deltas(new_delta, old_delta),
{
    if new_delta.0 == 0 {
        proof { assert(new_delta == crate::spec::Messages_t::nop_delta()); }
        old_delta
    } else if old_delta.0 == 0 {
        proof {
            assert(new_delta != crate::spec::Messages_t::nop_delta());
            assert(old_delta == crate::spec::Messages_t::nop_delta());
        }
        new_delta
    } else {
        proof {
            assert(new_delta != crate::spec::Messages_t::nop_delta());
            assert(old_delta != crate::spec::Messages_t::nop_delta());
        }
        new_delta
    }
}

pub fn merge_messages(older: Message, newer: Message) -> (out: Message)
    ensures out == older.merge(newer),
{
    match newer {
        Message::Define { value } => Message::Define { value },
        Message::Update { delta: new_delta } => match older {
            Message::Define { value } => {
                proof { assert(Message::apply_delta(new_delta, value) == value); }
                Message::Define { value }
            },
            Message::Update { delta: old_delta } => {
                let delta = combine_deltas(new_delta, old_delta);
                Message::Update { delta }
            },
        },
    }
}

pub open spec fn fold_branch_messages(
    messages: Seq<Message>,
    start: int,
) -> Message
    recommends 0 <= start <= messages.len(),
    decreases messages.len() - start when start <= messages.len()
{
    if start == messages.len() {
        Message::Update { delta: Delta(0) }
    } else {
        messages[start].merge(fold_branch_messages(messages, start + 1))
    }
}

fn fold_branch_messages_exec(messages: &Vec<Message>) -> (out: Message)
    ensures out == fold_branch_messages(messages@, 0),
{
    let mut out = Message::Update { delta: Delta(0) };
    let mut index = messages.len();
    while index > 0
        invariant
            index <= messages.len(),
            out == fold_branch_messages(messages@, index as int),
        decreases index,
    {
        index -= 1;
        out = merge_messages(messages[index], out);
    }
    out
}

pub open spec fn fold_betree_messages(
    messages: Seq<Message>,
    start: int,
) -> Message
    recommends 0 <= start < messages.len(),
    decreases messages.len() - start when start < messages.len()
{
    if start == messages.len() - 1 {
        Message::Define { value: default_value() }.merge(messages[start])
    } else {
        fold_betree_messages(messages, start + 1).merge(messages[start])
    }
}

fn fold_betree_messages_exec(messages: &Vec<Message>) -> (out: Message)
    requires messages.len() > 0,
    ensures out == fold_betree_messages(messages@, 0),
{
    let mut index = messages.len();
    let mut out = Message::Define { value: Value(0) };
    while index > 0
        invariant
            index <= messages.len(),
            index == messages.len()
                ==> out == (Message::Define { value: default_value() }),
            index < messages.len()
                ==> out == fold_betree_messages(messages@, index as int),
        decreases index,
    {
        index -= 1;
        out = merge_messages(out, messages[index]);
    }
    out
}

proof fn receipt_valid_after_union(
    cache: Cache::State,
    receipt: LoadedPathReceipt,
    root: Address,
    base: Map<Address, RawPage>,
    extra: Map<Address, RawPage>,
)
    requires
        receipt.valid_for(root, to_branch_nodes(base)),
        forall |addr: Address| #[trigger] base.contains_key(addr)
            ==> cache.valid_read(addr, base[addr]),
        forall |addr: Address| #[trigger] extra.contains_key(addr)
            ==> cache.valid_read(addr, extra[addr]),
    ensures receipt.valid_for(
        root,
        to_branch_nodes(base.union_prefer_right(extra)),
    ),
{
    let merged = base.union_prefer_right(extra);
    assert(receipt.needed_addrs() <= to_branch_nodes(merged).dom()) by {
        assert forall |addr: Address| #[trigger] receipt.needed_addrs().contains(addr)
            implies to_branch_nodes(merged).dom().contains(addr) by {
            assert(base.contains_key(addr));
            assert(merged.contains_key(addr));
        }
    }
    assert forall |i: int| 0 <= i < receipt.lines.len() implies {
        &&& to_branch_nodes(merged).contains_key(
            (#[trigger] receipt.lines[i]).addr,
        )
        &&& to_branch_nodes(merged)[receipt.lines[i].addr]
            == receipt.lines[i].node
    } by {
        let addr = receipt.lines[i].addr;
        assert(base.contains_key(addr));
        assert(to_branch_nodes(base)[addr] == receipt.lines[i].node);
        if extra.contains_key(addr) {
            Cache::State::valid_read_unique(
                cache,
                addr,
                base[addr],
                extra[addr],
            );
            assert(merged[addr] == extra[addr]);
            assert(extra[addr] == base[addr]);
        } else {
            assert(merged[addr] == base[addr]);
        }
        assert(raw_page_to_branch_node(merged[addr])
            == raw_page_to_branch_node(base[addr]));
        assert(to_branch_nodes(merged)[addr]
            == raw_page_to_branch_node(merged[addr]));
    }
}

proof fn valid_read_union_commutes(
    cache: Cache::State,
    left: Map<Address, RawPage>,
    right: Map<Address, RawPage>,
)
    requires
        forall |addr: Address| #[trigger] left.contains_key(addr)
            ==> cache.valid_read(addr, left[addr]),
        forall |addr: Address| #[trigger] right.contains_key(addr)
            ==> cache.valid_read(addr, right[addr]),
    ensures left.union_prefer_right(right)
        =~= right.union_prefer_right(left),
{
    assert_maps_equal!(
        left.union_prefer_right(right),
        right.union_prefer_right(left),
        addr => {
            if left.contains_key(addr) && right.contains_key(addr) {
                Cache::State::valid_read_unique(
                    cache,
                    addr,
                    left[addr],
                    right[addr],
                );
            }
        }
    );
}

proof fn branch_receipts_valid_after_union(
    cache: Cache::State,
    roots: crate::betree::LinkedSeq_v::LinkedSeq,
    start: nat,
    receipts: Seq<LoadedPathReceipt>,
    key: Key,
    base: Map<Address, RawPage>,
    extra: Map<Address, RawPage>,
)
    requires
        branch_receipts_valid(
            roots,
            start,
            receipts,
            key,
            to_branch_nodes(base),
        ),
        forall |addr: Address| #[trigger] base.contains_key(addr)
            ==> cache.valid_read(addr, base[addr]),
        forall |addr: Address| #[trigger] extra.contains_key(addr)
            ==> cache.valid_read(addr, extra[addr]),
    ensures branch_receipts_valid(
        roots,
        start,
        receipts,
        key,
        to_branch_nodes(base.union_prefer_right(extra)),
    ),
{
    assert forall |i: int| 0 <= i < receipts.len() implies {
        let receipt = #[trigger] receipts[i];
        let root = roots[start as int + i];
        &&& receipt.key == key
        &&& receipt.valid_for(
            root,
            to_branch_nodes(base.union_prefer_right(extra)),
        )
        &&& receipt.target().node is Leaf
    } by {
        receipt_valid_after_union(
            cache,
            receipts[i],
            roots[start as int + i],
            base,
            extra,
        );
    }
}

pub open spec fn branch_receipts_prefix_valid(
    roots: crate::betree::LinkedSeq_v::LinkedSeq,
    start: nat,
    receipts: Seq<LoadedPathReceipt>,
    key: Key,
    reads: Map<Address, RawPage>,
) -> bool {
    &&& start <= roots.len()
    &&& receipts.len() <= roots.len() - start
    &&& forall |i: int| 0 <= i < receipts.len() ==> {
        let receipt = #[trigger] receipts[i];
        let root = roots[start as int + i];
        &&& receipt.key == key
        &&& receipt.valid_for(root, to_branch_nodes(reads))
        &&& receipt.target().node is Leaf
    }
}

proof fn branch_receipts_prefix_valid_after_union(
    cache: Cache::State,
    roots: crate::betree::LinkedSeq_v::LinkedSeq,
    start: nat,
    receipts: Seq<LoadedPathReceipt>,
    key: Key,
    base: Map<Address, RawPage>,
    extra: Map<Address, RawPage>,
)
    requires
        branch_receipts_prefix_valid(
            roots,
            start,
            receipts,
            key,
            base,
        ),
        forall |addr: Address| #[trigger] base.contains_key(addr)
            ==> cache.valid_read(addr, base[addr]),
        forall |addr: Address| #[trigger] extra.contains_key(addr)
            ==> cache.valid_read(addr, extra[addr]),
    ensures branch_receipts_prefix_valid(
        roots,
        start,
        receipts,
        key,
        base.union_prefer_right(extra),
    ),
{
    assert forall |i: int| 0 <= i < receipts.len() implies {
        let receipt = #[trigger] receipts[i];
        let root = roots[start as int + i];
        &&& receipt.key == key
        &&& receipt.valid_for(
            root,
            to_branch_nodes(base.union_prefer_right(extra)),
        )
        &&& receipt.target().node is Leaf
    } by {
        receipt_valid_after_union(
            cache,
            receipts[i],
            roots[start as int + i],
            base,
            extra,
        );
    }
}

proof fn branch_receipts_prefix_is_full(
    roots: crate::betree::LinkedSeq_v::LinkedSeq,
    start: nat,
    receipts: Seq<LoadedPathReceipt>,
    key: Key,
    reads: Map<Address, RawPage>,
)
    requires
        branch_receipts_prefix_valid(roots, start, receipts, key, reads),
        receipts.len() == roots.len() - start,
    ensures branch_receipts_valid(roots, start, receipts, key, to_branch_nodes(reads)),
{
}

proof fn receipt_messages_match(
    receipts: Seq<LoadedPathReceipt>,
    messages: Seq<Message>,
    start: int,
)
    requires
        receipts.len() == messages.len(),
        forall |i: int| 0 <= i < receipts.len()
            ==> #[trigger] messages[i] == receipts[i].result(),
        0 <= start <= receipts.len(),
    ensures fold_branch_messages(messages, start)
        == branch_receipts_result(receipts, start),
    decreases receipts.len() - start,
{
    if start < receipts.len() {
        receipt_messages_match(receipts, messages, start + 1);
    }
}

proof fn betree_messages_match(
    receipt: LoadedBetreeQueryReceipt,
    messages: Seq<Message>,
    start: int,
)
    requires
        receipt.path.lines.len() > 0,
        receipt.buffer_receipts.len() == receipt.path.lines.len(),
        messages.len() == receipt.buffer_receipts.len(),
        forall |i: int| 0 <= i < messages.len() ==> {
            #[trigger] messages[i]
                == branch_receipts_result(receipt.buffer_receipts[i], 0)
        },
        0 <= start < messages.len(),
    ensures fold_betree_messages(messages, start)
        == receipt.result_at(start),
    decreases messages.len() - start,
{
    if start < messages.len() - 1 {
        betree_messages_match(receipt, messages, start + 1);
    }
}

proof fn fold_betree_messages_is_define(
    messages: Seq<Message>,
    start: int,
)
    requires 0 <= start < messages.len(),
    ensures fold_betree_messages(messages, start) is Define,
    decreases messages.len() - start,
{
    if start < messages.len() - 1 {
        fold_betree_messages_is_define(messages, start + 1);
    }
}

pub open spec fn betree_path_lines_wf(
    key: Key,
    root: Address,
    lines: Seq<LoadedBetreePathLine>,
) -> bool {
    &&& (lines.len() == 0 || lines[0].addr == root)
    &&& forall |i: int| 0 <= i < lines.len()
        ==> (#[trigger] lines[i]).wf()
    &&& forall |i: int| 0 <= i < lines.len()
        ==> (#[trigger] lines[i]).node.key_in_domain(key)
    &&& forall |i: int| 0 <= i < lines.len() - 1
        ==> (#[trigger] lines[i]).node.is_index()
    &&& forall |i: int| 0 <= i < lines.len() - 1 ==> {
        let line = lines[i];
        line.node.child_ptr(key)
            == Some((#[trigger] lines[i + 1]).addr)
    }
}

pub open spec fn betree_partial_path_wf(
    key: Key,
    root: Address,
    lines: Seq<LoadedBetreePathLine>,
    current: Address,
) -> bool {
    &&& betree_path_lines_wf(key, root, lines)
    &&& lines.len() == 0 ==> current == root
    &&& lines.len() > 0 ==> {
        let line = lines.last();
        &&& line.node.is_index()
        &&& line.node.child_ptr(key) == Some(current)
    }
}

pub proof fn betree_path_extend_line(
    key: Key,
    root: Address,
    lines: Seq<LoadedBetreePathLine>,
    current: Address,
    line: LoadedBetreePathLine,
)
    requires
        betree_partial_path_wf(key, root, lines, current),
        line.addr == current,
        line.wf(),
        line.node.key_in_domain(key),
    ensures betree_path_lines_wf(key, root, lines.push(line)),
{
    let extended = lines.push(line);
    assert forall |i: int| 0 <= i < extended.len() - 1
        implies (#[trigger] extended[i]).node.is_index() by {
        assert(i < lines.len());
        assert(extended[i] == lines[i]);
        if i == lines.len() - 1 {
            assert(lines[i] == lines.last());
        }
    }
    assert forall |i: int| 0 <= i < extended.len()
        implies (#[trigger] extended[i]).wf() by {
        if i == lines.len() {
            assert(extended[i] == line);
        } else {
            assert(extended[i] == lines[i]);
        }
    }
    assert forall |i: int| 0 <= i < extended.len()
        implies (#[trigger] extended[i]).node.key_in_domain(key) by {
        if i == lines.len() {
            assert(extended[i] == line);
        } else {
            assert(extended[i] == lines[i]);
        }
    }
    assert forall |i: int| 0 <= i < extended.len() - 1 implies {
        let current_line = extended[i];
        current_line.node.child_ptr(key)
            == Some((#[trigger] extended[i + 1]).addr)
    } by {
        if i == lines.len() - 1 {
            assert(extended[i] == lines.last());
            assert(extended[i + 1] == line);
            assert(lines.last().node.child_ptr(key) == Some(current));
        } else {
            assert(extended[i] == lines[i]);
            assert(extended[i + 1] == lines[i + 1]);
            assert(lines[i].node.child_ptr(key) == Some(lines[i + 1].addr));
        }
        assert(extended[i].node.child_ptr(key)
            == Some(extended[i + 1].addr));
    }
}

proof fn pointer_equal_some(pointer: Option<Address>, addr: Address)
    requires pointer == Some(addr),
    ensures
        pointer is Some,
        pointer.unwrap() == addr,
{
}

pub open spec fn loaded_buffer_receipts_valid(
    lines: Seq<LoadedBetreePathLine>,
    receipts: Seq<Seq<LoadedPathReceipt>>,
    key: Key,
    reads: Map<Address, RawPage>,
) -> bool {
    &&& receipts.len() == lines.len()
    &&& forall |i: int| 0 <= i < lines.len() ==> {
        let node = (#[trigger] lines[i]).node;
        branch_receipts_valid(
            node.buffers,
            node.flushed_ofs(key),
            receipts[i],
            key,
            to_branch_nodes(reads),
        )
    }
}

proof fn loaded_buffer_receipts_valid_after_union(
    cache: Cache::State,
    lines: Seq<LoadedBetreePathLine>,
    receipts: Seq<Seq<LoadedPathReceipt>>,
    key: Key,
    base: Map<Address, RawPage>,
    extra: Map<Address, RawPage>,
)
    requires
        loaded_buffer_receipts_valid(lines, receipts, key, base),
        forall |addr: Address| #[trigger] base.contains_key(addr)
            ==> cache.valid_read(addr, base[addr]),
        forall |addr: Address| #[trigger] extra.contains_key(addr)
            ==> cache.valid_read(addr, extra[addr]),
    ensures loaded_buffer_receipts_valid(
        lines,
        receipts,
        key,
        base.union_prefer_right(extra),
    ),
{
    assert forall |i: int| 0 <= i < lines.len() implies {
        let node = (#[trigger] lines[i]).node;
        branch_receipts_valid(
            node.buffers,
            node.flushed_ofs(key),
            receipts[i],
            key,
            to_branch_nodes(base.union_prefer_right(extra)),
        )
    } by {
        let node = lines[i].node;
        branch_receipts_valid_after_union(
            cache,
            node.buffers,
            node.flushed_ofs(key),
            receipts[i],
            key,
            base,
            extra,
        );
    }
}

pub proof fn extend_betree_read_preserves(
    cache: Cache::State,
    reads_pre: Map<Address, RawPage>,
    lines_pre: Seq<LoadedBetreePathLine>,
    current: Address,
    raw: RawPage,
    root: Address,
    line: LoadedBetreePathLine,
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

pub fn load_betree_query(
    cache: &mut FracCacheImpl,
    root: IAddress,
    key: Key,
    betree_fuel: usize,
    branch_fuel: usize,
    betree_aus: Ghost<Set<AU>>,
    branch_summary: Ghost<Map<AU, Summary>>,
    branch_aus: Ghost<Set<AU>>,
) -> (out: BetreeQueryResult)
    requires
        old(cache).wf(),
        betree_fuel > 0,
        branch_fuel > 0,
        cached_betree_query_valid(
            old(cache)@,
            root@,
            key,
            betree_fuel as nat,
            branch_fuel as nat,
            betree_aus@,
            branch_summary@,
            branch_aus@,
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
            BetreeQueryResult::Loaded {
                value,
                disk_message,
                betree_reads,
                branch_reads,
                receipt,
            } => {
                let raw_reads = betree_reads@.union_prefer_right(branch_reads@);
                &&& cache@ == old(cache)@
                &&& receipt@.valid_for(
                    Some(root@),
                    key,
                    to_betree_nodes(betree_reads@),
                    to_branch_nodes(branch_reads@),
                )
                &&& disk_message == receipt@.result()
                &&& disk_message == Message::Define { value }
                &&& betree_reads@.dom()
                    <= addresses_in_aus(betree_aus@)
                &&& branch_reads@.dom()
                    <= addresses_in_aus(branch_aus@)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    Cache::Label::Access {
                        reads: raw_reads,
                        writes: Map::empty(),
                    },
                )
            },
            BetreeQueryResult::NeedCacheLoad { addr, handle } => {
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, handle)
                &&& (betree_aus@ + branch_aus@).contains(addr@.au)
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                )
            },
            BetreeQueryResult::CacheFull
            | BetreeQueryResult::Blocked
            | BetreeQueryResult::InvalidPage => cache@ == old(cache)@,
        },
{
    let ghost cache0 = *cache;
    let ghost root_addr = root@;
    let ghost mut betree_reads = Map::<Address, RawPage>::empty();
    let ghost mut branch_reads = Map::<Address, RawPage>::empty();
    let ghost mut lines = Seq::<LoadedBetreePathLine>::empty();
    let ghost mut buffer_receipts = Seq::<Seq<LoadedPathReceipt>>::empty();
    let mut buffered_messages = Vec::<Message>::new();
    let mut current = root;
    let mut remaining = betree_fuel;

    while remaining > 0
        invariant
            cache.wf(),
            cache@ == cache0@,
            cache.valid_load_handles_preserved(cache0),
            0 < remaining <= betree_fuel,
            cached_betree_query_valid(
                cache0@,
                current@,
                key,
                remaining as nat,
                branch_fuel as nat,
                betree_aus@,
                branch_summary@,
                branch_aus@,
            ),
            betree_partial_path_wf(key, root_addr, lines, current@),
            betree_reads.dom() == Set::new(|addr: Address| exists |i: int|
                0 <= i < lines.len() && #[trigger] lines[i].addr == addr),
            forall |i: int| 0 <= i < lines.len() ==> {
                &&& betree_reads.contains_key((#[trigger] lines[i]).addr)
                &&& to_betree_nodes(betree_reads)[lines[i].addr]
                    == lines[i].node
            },
            forall |addr: Address| #[trigger] betree_reads.contains_key(addr)
                ==> cache0@.valid_read(addr, betree_reads[addr]),
            forall |addr: Address| #[trigger] branch_reads.contains_key(addr)
                ==> cache0@.valid_read(addr, branch_reads[addr]),
            betree_reads.dom() <= addresses_in_aus(betree_aus@),
            branch_reads.dom()
                <= addresses_in_aus(branch_aus@),
            loaded_buffer_receipts_valid(
                lines,
                buffer_receipts,
                key,
                branch_reads,
            ),
            buffered_messages@.len() == buffer_receipts.len(),
            forall |i: int| 0 <= i < buffered_messages@.len()
                ==> #[trigger] buffered_messages@[i]
                    == branch_receipts_result(buffer_receipts[i], 0),
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
                return BetreeQueryResult::NeedCacheLoad {
                    addr: current,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::Success { slot_handle } => {
                let ghost raw = slot_handle.rec@;
                let ghost fetched_slot = slot_handle.idx;
                let fmt = BetreeNodePageFmt::new();
                let all_slice = Slice::all(&slot_handle.rec);
                let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                proof {
                    assert(cache_pre_fetch@ == cache0@);
                    assert(cache0@.valid_read(current@, raw));
                    if parsed is Some {
                        assert(fmt == BetreeNodePageFmt::spec_new());
                        assert(all_slice@.i(slot_handle.rec@) == raw);
                        assert(fmt.parsable(all_slice@.i(slot_handle.rec@)));
                        assert(BetreeNodePageFmt::spec_new().parsable(raw));
                        assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                        assert(raw_page_to_betree_node(raw) == parsed.unwrap()@);
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
                    None => return BetreeQueryResult::InvalidPage,
                };
                let ghost node_view = node@;
                let ghost line = LoadedBetreePathLine {
                    addr: current@,
                    node: node_view,
                };
                let ghost reads_pre = betree_reads;
                let ghost lines_pre = lines;
                proof {
                    assert(cached_betree_query_valid(
                        cache0@,
                        current@,
                        key,
                        remaining as nat,
                        branch_fuel as nat,
                        betree_aus@,
                        branch_summary@,
                        branch_aus@,
                    ));
                    assert({
                        let parsed_view = raw_page_to_betree_node(raw);
                        &&& parsed_view.key_in_domain(key)
                        &&& forall |i: int|
                            parsed_view.flushed_ofs(key) <= i
                                < parsed_view.buffers.len()
                            ==> {
                                let buffer_root = #[trigger]
                                    parsed_view.buffers.addrs[i];
                                &&& branch_summary@.contains_key(
                                    buffer_root.au,
                                )
                                &&& branch_summary@[buffer_root.au]
                                    <= branch_aus@
                                &&& cached_branch_path_valid(
                                    cache0@,
                                    buffer_root,
                                    key,
                                    branch_fuel as nat,
                                    branch_summary@[buffer_root.au],
                                )
                            }
                        &&& match parsed_view.child_ptr(key) {
                            Some(child) => {
                                cached_betree_query_valid(
                                    cache0@,
                                    child,
                                    key,
                                    (remaining as nat - 1) as nat,
                                    branch_fuel as nat,
                                    betree_aus@,
                                    branch_summary@,
                                    branch_aus@,
                                )
                            },
                            None => true,
                        }
                    });
                    assert(node_view.key_in_domain(key));
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
                    betree_reads = betree_reads.insert(current@, raw);
                    lines = lines.push(line);
                    assert(betree_aus@.contains(current@.au));
                    assert(betree_reads.dom()
                        <= addresses_in_aus(betree_aus@)) by {
                        assert forall |addr: Address|
                            #[trigger] betree_reads.dom().contains(addr)
                            implies addresses_in_aus(betree_aus@).contains(addr) by {
                            if addr != current@ {
                                assert(reads_pre.dom().contains(addr));
                            }
                        }
                    }
                    assert(to_betree_nodes(betree_reads)[current@]
                        == node_view);
                    assert forall |i: int| 0 <= i < lines.len() implies {
                        &&& betree_reads.contains_key((#[trigger] lines[i]).addr)
                        &&& to_betree_nodes(betree_reads)[lines[i].addr]
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

                proof {
                    assert(node_view.wf());
                    assert(node_view.pivots.wf());
                    assert(node_view.pivots.pivots
                        == Parsedview::<Seq<Element>>::parsedv(&node.pivots));
                    Element::strictly_sorted_implies_sorted(
                        node_view.pivots.pivots,
                    );
                }
                let route = betree_route_index(&node.pivots, key);
                proof {
                    assert((route as int) == Element::largest_lte(
                        Parsedview::<Seq<Element>>::parsedv(&node.pivots),
                        to_element(key),
                    ));
                    assert(Parsedview::<Seq<Element>>::parsedv(&node.pivots)
                        == node_view.pivots.pivots);
                    assert(node_view.pivots.bounded_key(key));
                    assert(node_view.pivots.route(key)
                        == Element::largest_lte(
                            node_view.pivots.pivots,
                            to_element(key),
                        ));
                    assert((route as int) == node_view.pivots.route(key));
                    node_view.pivots.route_lemma(key);
                    assert(0 <= route as int);
                    assert((route as int) < node_view.children.len());
                    assert(route < node.flushed.len());
                }
                let start = node.flushed[route] as usize;
                proof {
                    assert(start as nat == node_view.flushed.offsets[route as int]);
                    assert(start <= node.buffers.len());
                    assert(start as nat == node_view.flushed_ofs(key));
                }
                let ghost mut current_receipts = Seq::<LoadedPathReceipt>::empty();
                let mut current_messages = Vec::<Message>::new();
                let mut buffer_index = start;
                proof {
                    assert(branch_receipts_prefix_valid(
                        node_view.buffers,
                        start as nat,
                        current_receipts,
                        key,
                        branch_reads,
                    ));
                }
                while buffer_index < node.buffers.len()
                    invariant
                        cache.wf(),
                        cache@ == cache0@,
                        cache.valid_load_handles_preserved(cache0),
                        start <= buffer_index <= node.buffers.len(),
                        node_view.buffers.addrs.len() == node.buffers.len(),
                        node_view.flushed_ofs(key) == start as nat,
                        current_receipts.len() == buffer_index - start,
                        current_messages@.len() == current_receipts.len(),
                        forall |i: int| 0 <= i < current_messages@.len()
                            ==> #[trigger] current_messages@[i]
                                == current_receipts[i].result(),
                        branch_receipts_prefix_valid(
                            node_view.buffers,
                            start as nat,
                            current_receipts,
                            key,
                            branch_reads,
                        ),
                        forall |addr: Address|
                            #[trigger] branch_reads.contains_key(addr)
                            ==> cache0@.valid_read(addr, branch_reads[addr]),
                        branch_reads.dom()
                            <= addresses_in_aus(branch_aus@),
                        loaded_buffer_receipts_valid(
                            lines_pre,
                            buffer_receipts,
                            key,
                            branch_reads,
                        ),
                    decreases node.buffers.len() - buffer_index,
                {
                    let branch_root = node.buffers[buffer_index];
                    let ghost root_summary = branch_summary@[branch_root@.au];
                    proof {
                        assert(node_view.buffers.addrs[buffer_index as int]
                            == branch_root@);
                        assert(node_view.flushed_ofs(key)
                            <= buffer_index as int);
                        assert((buffer_index as int)
                            < node_view.buffers.len());
                        assert(branch_summary@.contains_key(branch_root@.au));
                        assert(root_summary <= branch_aus@);
                        assert(cached_branch_path_valid(
                            cache0@,
                            branch_root@,
                            key,
                            branch_fuel as nat,
                            root_summary,
                        ));
                    }
                    match load_branch_path(
                        cache,
                        branch_root,
                        key,
                        branch_fuel,
                        Ghost(root_summary),
                    ) {
                        BranchPathQueryResult::NeedCacheLoad {
                            addr,
                            handle,
                        } => {
                            proof {
                                assert(cache.valid_load_handles_preserved(cache0));
                                assert(root_summary.contains(addr@.au));
                                assert(branch_aus@.contains(addr@.au));
                            }
                            return BetreeQueryResult::NeedCacheLoad {
                                addr,
                                handle,
                            };
                        },
                        BranchPathQueryResult::CacheFull => {
                            return BetreeQueryResult::CacheFull;
                        },
                        BranchPathQueryResult::Blocked => {
                            return BetreeQueryResult::Blocked;
                        },
                        BranchPathQueryResult::InvalidPage => {
                            return BetreeQueryResult::InvalidPage;
                        },
                        BranchPathQueryResult::Loaded {
                            message,
                            reads: local_reads,
                            receipt,
                        } => {
                            let ghost reads_before = branch_reads;
                            let ghost receipts_before = current_receipts;
                            let ghost messages_before = current_messages@;
                            proof {
                                assert(cache@ == cache0@);
                                assert forall |addr: Address|
                                    #[trigger] local_reads@.contains_key(addr)
                                    implies cache0@.valid_read(
                                        addr,
                                        local_reads@[addr],
                                    ) by {
                                    Cache::State::access_read_valid(
                                        cache0@,
                                        cache0@,
                                        local_reads@,
                                        Map::empty(),
                                        addr,
                                    );
                                }
                                loaded_buffer_receipts_valid_after_union(
                                    cache0@,
                                    lines_pre,
                                    buffer_receipts,
                                    key,
                                    reads_before,
                                    local_reads@,
                                );
                                branch_receipts_prefix_valid_after_union(
                                    cache0@,
                                    node_view.buffers,
                                    start as nat,
                                    receipts_before,
                                    key,
                                    reads_before,
                                    local_reads@,
                                );
                                receipt_valid_after_union(
                                    cache0@,
                                    receipt@,
                                    branch_root@,
                                    local_reads@,
                                    reads_before,
                                );
                                valid_read_union_commutes(
                                    cache0@,
                                    reads_before,
                                    local_reads@,
                                );
                                branch_reads = reads_before.union_prefer_right(
                                    local_reads@,
                                );
                                current_receipts = receipts_before.push(receipt@);
                                assert(receipt@.valid_for(
                                    branch_root@,
                                    to_branch_nodes(branch_reads),
                                ));
                                assert(branch_receipts_prefix_valid(
                                    node_view.buffers,
                                    start as nat,
                                    current_receipts,
                                    key,
                                    branch_reads,
                                )) by {
                                    assert forall |i: int|
                                        0 <= i < current_receipts.len()
                                        implies {
                                            let current_receipt = #[trigger]
                                                current_receipts[i];
                                            let current_root = node_view.buffers[
                                                start as int + i
                                            ];
                                            &&& current_receipt.key == key
                                            &&& current_receipt.valid_for(
                                                current_root,
                                                to_branch_nodes(branch_reads),
                                            )
                                            &&& current_receipt.target().node is Leaf
                                        } by {
                                        if i == receipts_before.len() {
                                            assert(current_receipts[i] == receipt@);
                                            assert(node_view.buffers[
                                                start as int + i
                                            ] == branch_root@);
                                        } else {
                                            assert(current_receipts[i]
                                                == receipts_before[i]);
                                        }
                                    }
                                }
                                assert(branch_reads.dom()
                                    <= addresses_in_aus(branch_aus@)) by {
                                    assert forall |addr: Address|
                                        #[trigger] branch_reads.dom().contains(addr)
                                        implies addresses_in_aus(
                                            branch_aus@,
                                        ).contains(addr) by {
                                        if local_reads@.contains_key(addr) {
                                            assert(addresses_in_aus(root_summary)
                                                .contains(addr));
                                            assert(root_summary.contains(addr.au));
                                            assert(branch_aus@.contains(addr.au));
                                        } else {
                                            assert(reads_before.dom().contains(addr));
                                        }
                                    }
                                }
                                assert forall |addr: Address|
                                    #[trigger] branch_reads.contains_key(addr)
                                    implies cache0@.valid_read(
                                        addr,
                                        branch_reads[addr],
                                    ) by {
                                    if local_reads@.contains_key(addr) {
                                    } else {
                                        assert(reads_before.contains_key(addr));
                                    }
                                }
                            }
                            current_messages.push(message);
                            proof {
                                assert(current_messages@
                                    == messages_before.push(message));
                                assert(message == receipt@.result());
                                assert forall |i: int|
                                    0 <= i < current_messages@.len()
                                    implies #[trigger] current_messages@[i]
                                        == current_receipts[i].result() by {
                                    if i == messages_before.len() {
                                    } else {
                                        assert(current_messages@[i]
                                            == messages_before[i]);
                                        assert(current_receipts[i]
                                            == receipts_before[i]);
                                    }
                                }
                            }
                            buffer_index += 1;
                        },
                    }
                }

                let buffered = fold_branch_messages_exec(&current_messages);
                let ghost receipts_pre = buffer_receipts;
                let ghost buffered_pre = buffered_messages@;
                proof {
                    assert(current_receipts.len()
                        == node_view.buffers.len() - start as nat);
                    branch_receipts_prefix_is_full(
                        node_view.buffers,
                        start as nat,
                        current_receipts,
                        key,
                        branch_reads,
                    );
                    receipt_messages_match(
                        current_receipts,
                        current_messages@,
                        0,
                    );
                    assert(buffered
                        == branch_receipts_result(current_receipts, 0));
                    buffer_receipts = buffer_receipts.push(current_receipts);
                    assert(loaded_buffer_receipts_valid(
                        lines,
                        buffer_receipts,
                        key,
                        branch_reads,
                    )) by {
                        assert forall |i: int| 0 <= i < lines.len() implies {
                            let path_node = (#[trigger] lines[i]).node;
                            branch_receipts_valid(
                                path_node.buffers,
                                path_node.flushed_ofs(key),
                                buffer_receipts[i],
                                key,
                                to_branch_nodes(branch_reads),
                            )
                        } by {
                            if i == lines.len() - 1 {
                                assert(lines[i] == line);
                                assert(buffer_receipts[i] == current_receipts);
                            } else {
                                assert(i < lines_pre.len());
                                assert(buffer_receipts[i] == receipts_pre[i]);
                            }
                        }
                    }
                }
                buffered_messages.push(buffered);
                proof {
                    assert(buffered_messages@
                        == buffered_pre.push(buffered));
                    assert forall |i: int|
                        0 <= i < buffered_messages@.len()
                        implies #[trigger] buffered_messages@[i]
                            == branch_receipts_result(
                                buffer_receipts[i],
                                0,
                            ) by {
                        if i == buffered_pre.len() {
                        } else {
                            assert(buffered_messages@[i] == buffered_pre[i]);
                            assert(buffer_receipts[i] == receipts_pre[i]);
                        }
                    }
                }

                match node.children[route] {
                    Some(child) => {
                        if !is_index_node(&node) {
                            proof { assert(cache@ == cache0@); }
                            return BetreeQueryResult::Blocked;
                        }
                        proof {
                            assert(node_view.child_ptr(key) == Some(child@));
                            assert(node_view.is_index());
                        }
                        remaining -= 1;
                        if remaining == 0 {
                            proof { assert(cache@ == cache0@); }
                            return BetreeQueryResult::Blocked;
                        }
                        current = child;
                        proof {
                            assert(lines.last() == line);
                            assert(line.node.child_ptr(key) == Some(current@));
                            assert(line.node.is_index());
                            assert(betree_partial_path_wf(
                                key,
                                root_addr,
                                lines,
                                current@,
                            ));
                            assert(cached_betree_query_valid(
                                cache0@,
                                current@,
                                key,
                                remaining as nat,
                                branch_fuel as nat,
                                betree_aus@,
                                branch_summary@,
                                branch_aus@,
                            ));
                        }
                    },
                    None => {
                        let ghost path = LoadedBetreePath {
                            key,
                            root: root_addr,
                            lines,
                        };
                        let ghost receipt = LoadedBetreeQueryReceipt {
                            path,
                            buffer_receipts,
                        };
                        let disk_message = fold_betree_messages_exec(
                            &buffered_messages,
                        );
                        proof {
                            assert(betree_path_lines_wf(key, root_addr, lines));
                            assert forall |i: int| 0 <= i < lines.len() - 1
                                implies {
                                    let path_line = lines[i];
                                    &&& path_line.node.child_ptr(key) is Some
                                    &&& path_line.node.child_ptr(key).unwrap()
                                        == (#[trigger] lines[i + 1]).addr
                                } by {
                                assert(lines[i].node.child_ptr(key)
                                    == Some(lines[i + 1].addr));
                            }
                            assert(path.lines == lines);
                            assert(path.key == key);
                            assert forall |i: int| 0 <= i < path.lines.len() - 1
                                implies (#[trigger] path.lines[i]).node
                                    .child_ptr(path.key) is Some by {
                                assert(path.lines[i].node.child_ptr(path.key)
                                    == Some(path.lines[i + 1].addr));
                                pointer_equal_some(
                                    path.lines[i].node.child_ptr(path.key),
                                    path.lines[i + 1].addr,
                                );
                            }
                            assert forall |i: int| 0 <= i < path.lines.len() - 1
                                implies {
                                    let path_line = path.lines[i];
                                    &&& path_line.node.child_ptr(path.key) is Some
                                    &&& path_line.node.child_ptr(path.key).unwrap()
                                        == (#[trigger] path.lines[i + 1]).addr
                            } by {
                                assert(path.lines[i].node.child_ptr(path.key)
                                    == Some(path.lines[i + 1].addr));
                                pointer_equal_some(
                                    path.lines[i].node.child_ptr(path.key),
                                    path.lines[i + 1].addr,
                                );
                            }
                            assert(path.wf());
                            assert(path.valid_for(
                                Some(root_addr),
                                to_betree_nodes(betree_reads),
                            ));
                            assert(path.target() == line);
                            assert(path.target().node.child_ptr(key) is None);
                            assert(receipt.valid_for(
                                Some(root_addr),
                                key,
                                to_betree_nodes(betree_reads),
                                to_branch_nodes(branch_reads),
                            ));
                            betree_messages_match(
                                receipt,
                                buffered_messages@,
                                0,
                            );
                            assert(disk_message == receipt.result());
                            fold_betree_messages_is_define(
                                buffered_messages@,
                                0,
                            );
                            assert(disk_message is Define);
                            let raw_reads = betree_reads.union_prefer_right(
                                branch_reads,
                            );
                            assert forall |addr: Address|
                                #[trigger] raw_reads.contains_key(addr)
                                implies cache0@.valid_read(
                                    addr,
                                    raw_reads[addr],
                                ) by {
                                if branch_reads.contains_key(addr) {
                                } else {
                                    assert(betree_reads.contains_key(addr));
                                }
                            }
                            Cache::State::access_read_only_from_valid_reads(
                                cache0@,
                                raw_reads,
                            );
                        }
                        let value = match disk_message {
                            Message::Define { value } => value,
                            Message::Update { delta: _ } => {
                                proof { assert(false); }
                                Value(0)
                            },
                        };
                        return BetreeQueryResult::Loaded {
                            value,
                            disk_message,
                            betree_reads: Ghost(betree_reads),
                            branch_reads: Ghost(branch_reads),
                            receipt: Ghost(receipt),
                        };
                    },
                }
            },
            FetchErrorCode::CacheFull => {
                return BetreeQueryResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BetreeQueryResult::Blocked;
            },
        }
    }
    proof { assert(cache@ == cache0@); }
    BetreeQueryResult::Blocked
}

} // verus!
