// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::implementation::IBranchNode_v::{IBranchNode, iaddr_seq};
use crate::implementation::FracCacheImpl_v::PAGE_SIZE_BYTES;
use crate::marshalling::IBranchNodeFormat_v::{
    BranchNodePageFmt, IBranchIndexMeta, IBranchIndexRoute,
    leaf_entry_seq, raw_page_to_branch_node, route_image_seq,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;

verus! {

pub open spec fn branch_leaf_capacity_spec() -> int {
    let format_capacity = BranchNodePageFmt::spec_new().leaf_fmt.max_length;
    if format_capacity <= u8::MAX as int {
        format_capacity as int
    } else {
        u8::MAX as int
    }
}

pub open spec fn branch_index_capacity_spec() -> int {
    let format_capacity = BranchNodePageFmt::spec_new().index_routes_fmt.max_length;
    if format_capacity <= u8::MAX as int {
        format_capacity as int
    } else {
        u8::MAX as int
    }
}

pub fn branch_leaf_capacity() -> (capacity: usize)
    ensures
        capacity as int == branch_leaf_capacity_spec(),
        capacity as int
            <= BranchNodePageFmt::spec_new().leaf_fmt.max_length,
        capacity <= u8::MAX as usize,
{
    let fmt = BranchNodePageFmt::new();
    let format_capacity = fmt.leaf_fmt.max_length;
    if format_capacity <= u8::MAX as usize {
        format_capacity
    } else {
        u8::MAX as usize
    }
}

pub fn branch_index_capacity() -> (capacity: usize)
    ensures
        capacity as int == branch_index_capacity_spec(),
        capacity as int
            <= BranchNodePageFmt::spec_new().index_routes_fmt.max_length,
        capacity <= u8::MAX as usize,
{
    let fmt = BranchNodePageFmt::new();
    let format_capacity = fmt.index_routes_fmt.max_length;
    if format_capacity <= u8::MAX as usize {
        format_capacity
    } else {
        u8::MAX as usize
    }
}

pub fn branch_node_is_full(node: &IBranchNode) -> (full: bool)
    requires node.wf(),
    ensures
        full == match node {
            IBranchNode::Leaf { keys, .. } => {
                keys@.len() >= branch_leaf_capacity_spec()
            },
            IBranchNode::Index { pivots, .. } => {
                pivots@.len() >= branch_index_capacity_spec()
            },
            IBranchNode::Auxiliary { .. } => false,
        },
{
    match node {
        IBranchNode::Leaf { keys, .. } => {
            keys.len() >= branch_leaf_capacity()
        },
        IBranchNode::Index { pivots, .. } => {
            pivots.len() >= branch_index_capacity()
        },
        IBranchNode::Auxiliary { .. } => false,
    }
}

pub proof fn leaf_branch_node_marshallable(node: &IBranchNode)
    requires
        node.wf(),
        node is Leaf,
        node->keys.len()
            <= BranchNodePageFmt::spec_new().leaf_fmt.max_length,
        node->keys.len() <= u8::MAX as int,
    ensures
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv())
            == PAGE_SIZE_BYTES,
{
    let fmt = BranchNodePageFmt::spec_new();
    match node {
        IBranchNode::Leaf { keys, msgs } => {
            let entries = leaf_entry_seq(keys@, msgs@);
            assert(keys.len() == msgs.len());
            assert(entries.len() == keys@.len());
            fmt.leaf_fmt.eltf.uniform_size_matches_spec_size();
            assert forall |i: int| 0 <= i < entries.len()
                implies #[trigger] fmt.leaf_fmt.marshallable_at(entries, i) by {
                assert(entries[i].key == keys@[i]);
                assert(entries[i].msg == msgs@[i]);
                assert(fmt.leaf_fmt.eltf.marshallable(entries[i]));
                assert(fmt.leaf_fmt.eltf.spec_size(entries[i])
                    == fmt.leaf_fmt.eltf.uniform_size());
            }
            assert(entries.len() <= u8::MAX as int);
            assert(entries.len() <= fmt.leaf_fmt.max_length);
            assert(fmt.leaf_fmt.marshallable(entries));
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(*node));
            assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
            assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
        },
        _ => {},
    }
}

pub proof fn index_branch_node_marshallable(node: &IBranchNode)
    requires
        node.wf(),
        node is Index,
        node->pivots.len()
            <= BranchNodePageFmt::spec_new().index_routes_fmt.max_length,
        node->pivots.len() <= u8::MAX as int,
    ensures
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv())
            == PAGE_SIZE_BYTES,
{
    let fmt = BranchNodePageFmt::spec_new();
    match node {
        IBranchNode::Index { pivots, children, aux_ptr } => {
            let routes = route_image_seq(pivots@, iaddr_seq(children@));
            assert(children.len() == pivots.len() + 1);
            assert(routes.len() == pivots@.len());
            fmt.index_routes_fmt.eltf.uniform_size_matches_spec_size();
            assert forall |i: int| 0 <= i < routes.len()
                implies #[trigger] fmt.index_routes_fmt.marshallable_at(
                    routes,
                    i,
                ) by {
                assert(routes[i].pivot == pivots@[i]);
                assert(routes[i].child == children@[i + 1]@);
                assert(fmt.index_routes_fmt.eltf.marshallable(routes[i]));
                assert(fmt.index_routes_fmt.eltf.spec_size(routes[i])
                    == fmt.index_routes_fmt.eltf.uniform_size());
            }
            assert(routes.len() <= u8::MAX as int);
            assert(routes.len() <= fmt.index_routes_fmt.max_length);
            assert(fmt.index_routes_fmt.marshallable(routes));
            assert(fmt.index_meta_fmt.impl_marshallable(IBranchIndexMeta {
                first_child: children[0],
                aux_ptr: *aux_ptr,
            }));
            assert forall |i: int| 0 <= i < pivots.len()
                implies #[trigger] fmt.index_routes_fmt.eltf.impl_marshallable(
                    IBranchIndexRoute {
                        pivot: pivots[i],
                        child: children[i + 1],
                    },
                ) by {
                assert(pivots[i].wf());
                assert(children[i + 1].wf());
            }
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(*node));
            assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
            assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
        },
        _ => {},
    }
}

pub proof fn auxiliary_branch_node_marshallable(node: &IBranchNode)
    requires
        node.wf(),
        node is Auxiliary,
        node->summary_aus.len()
            <= BranchNodePageFmt::spec_new().aux_fmt.max_length,
        node->summary_aus.len() <= u8::MAX as int,
    ensures
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv())
            == PAGE_SIZE_BYTES,
{
    let fmt = BranchNodePageFmt::spec_new();
    match node {
        IBranchNode::Auxiliary { summary_aus } => {
            let aus = summary_aus@.map(|i: int, au: u32| au as nat);
            assert(aus.len() == summary_aus@.len());
            fmt.aux_fmt.eltf.uniform_size_matches_spec_size();
            assert forall |i: int| 0 <= i < aus.len()
                implies #[trigger] fmt.aux_fmt.marshallable_at(aus, i) by {
                assert(aus[i] == summary_aus@[i] as nat);
                assert(fmt.aux_fmt.eltf.impl_marshallable(summary_aus[i]));
                assert(fmt.aux_fmt.eltf.marshallable(aus[i]));
                assert(fmt.aux_fmt.eltf.spec_size(aus[i])
                    == fmt.aux_fmt.eltf.uniform_size());
            }
            assert(aus.len() <= u8::MAX as int);
            assert(aus.len() <= fmt.aux_fmt.max_length);
            assert(fmt.aux_fmt.marshallable(aus));
            assert(fmt.marshallable(node.parsedv()));
            assert(fmt.impl_marshallable(*node));
            assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
            assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
        },
        _ => {},
    }
}

pub fn marshall_branch_node_page(node: &IBranchNode) -> (out: Vec<u8>)
    requires
        node.wf(),
        BranchNodePageFmt::spec_new().marshallable(node.parsedv()),
        BranchNodePageFmt::spec_new().impl_marshallable(*node),
        BranchNodePageFmt::spec_new().spec_size(node.parsedv())
            == PAGE_SIZE_BYTES,
    ensures
        out.len() == PAGE_SIZE_BYTES,
        BranchNodePageFmt::spec_new().parsable(out@),
        raw_page_to_branch_node(out@) == node@,
{
    let fmt = BranchNodePageFmt::new();
    let mut out = vec![0u8; PAGE_SIZE_BYTES];
    let end = fmt.exec_marshall(node, &mut out, 0);
    proof {
        assert(fmt == BranchNodePageFmt::spec_new());
        assert(end == PAGE_SIZE_BYTES);
        assert(out@.subrange(0, end as int) == out@);
        assert(fmt.parsable(out@));
        assert(fmt.parse(out@) == node.parsedv());
        assert(raw_page_to_branch_node(out@) == node@);
    }
    out
}

} // verus!
