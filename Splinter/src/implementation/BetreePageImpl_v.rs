// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::implementation::FracCacheImpl_v::PAGE_SIZE_BYTES;
use crate::implementation::IBetreeNode_v::IBetreeNode;
use crate::implementation::IBetreeNode_v::IElement;
use crate::marshalling::IBetreeNodeFormat_v::{
    BetreeNodePageFmt, raw_page_to_betree_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::disk::GenericDisk_v::Address;
use crate::spec::ImplDisk_t::{IAddress, IAU};

verus! {

pub open spec fn betree_node_addr(addr: Address) -> bool {
    addr.page == 0
}

pub fn betree_addr_for_au(au: IAU) -> (addr: IAddress)
    ensures
        addr.au == au,
        addr.page == 0,
        addr@ == (Address { au: au as nat, page: 0 }),
        betree_node_addr(addr@),
{
    IAddress { au, page: 0 }
}

pub proof fn bounded_betree_node_marshallable(node: &IBetreeNode)
    requires
        node.wf(),
        node@.wf(),
        node.buffers@.len()
            <= BetreeNodePageFmt::spec_new().buffers_fmt.max_length,
        node.pivots@.len()
            <= BetreeNodePageFmt::spec_new().pivots_fmt.max_length,
        node.children@.len()
            <= BetreeNodePageFmt::spec_new().children_fmt.max_length,
        node.flushed@.len()
            <= BetreeNodePageFmt::spec_new().flushed_fmt.max_length,
        node.buffers@.len() <= u8::MAX as int,
        node.pivots@.len() <= u8::MAX as int,
        node.children@.len() <= u8::MAX as int,
        node.flushed@.len() <= u8::MAX as int,
    ensures
        BetreeNodePageFmt::spec_new().marshallable(node.parsedv()),
        BetreeNodePageFmt::spec_new().impl_marshallable(*node),
        BetreeNodePageFmt::spec_new().spec_size(node.parsedv())
            == PAGE_SIZE_BYTES,
{
    let fmt = BetreeNodePageFmt::spec_new();
    fmt.buffers_fmt.eltf.uniform_size_matches_spec_size();
    fmt.pivots_fmt.eltf.uniform_size_matches_spec_size();
    fmt.children_fmt.eltf.f.uniform_size_matches_spec_size();
    fmt.flushed_fmt.eltf.uniform_size_matches_spec_size();
    assert forall |i: int| 0 <= i < node.buffers@.len()
        implies #[trigger] fmt.buffers_fmt.marshallable_at(
            node@.buffers.addrs,
            i,
        ) by {
        assert(node@.buffers.addrs[i] == node.buffers@[i]@);
        assert(fmt.buffers_fmt.eltf.marshallable(node@.buffers.addrs[i]));
        assert(fmt.buffers_fmt.eltf.spec_size(node@.buffers.addrs[i])
            == fmt.buffers_fmt.eltf.uniform_size());
    }
    assert forall |i: int| 0 <= i < node.pivots@.len()
        implies #[trigger] fmt.pivots_fmt.marshallable_at(
            node@.pivots.pivots,
            i,
        ) by {
        assert(node@.pivots.pivots[i] == node.pivots@[i]@);
        assert(fmt.pivots_fmt.eltf.marshallable(node@.pivots.pivots[i]));
        assert(fmt.pivots_fmt.eltf.spec_size(node@.pivots.pivots[i])
            == fmt.pivots_fmt.eltf.uniform_size());
    }
    assert forall |i: int| 0 <= i < node.children@.len()
        implies #[trigger] fmt.children_fmt.marshallable_at(
            node@.children,
            i,
        ) by {
        assert(node@.children[i]
            == Parsedview::parsedv(&node.children@[i]));
        assert(fmt.children_fmt.eltf.marshallable(node@.children[i]));
        assert(fmt.children_fmt.eltf.spec_size(node@.children[i])
            == fmt.children_fmt.eltf.uniform_size());
    }
    assert forall |i: int| 0 <= i < node.flushed@.len()
        implies #[trigger] fmt.flushed_fmt.marshallable_at(
            node@.flushed.offsets,
            i,
        ) by {
        assert(node@.flushed.offsets[i] == node.flushed@[i] as nat);
        assert(fmt.flushed_fmt.eltf.marshallable(node@.flushed.offsets[i]));
        assert(fmt.flushed_fmt.eltf.spec_size(node@.flushed.offsets[i])
            == fmt.flushed_fmt.eltf.uniform_size());
    }
    assert(fmt.buffers_fmt.marshallable(node@.buffers.addrs));
    assert(fmt.pivots_fmt.marshallable(node@.pivots.pivots));
    assert(fmt.children_fmt.marshallable(node@.children));
    assert(fmt.flushed_fmt.marshallable(node@.flushed.offsets));
    assert(fmt.marshallable(node.parsedv()));
    assert(fmt.impl_marshallable(*node));
    assert(fmt.spec_size(node.parsedv()) == fmt.uniform_size());
    assert(fmt.uniform_size() == PAGE_SIZE_BYTES);
}

pub fn build_initial_betree_root(
    branch_root: IAddress,
) -> (out: Option<IBetreeNode>)
    requires branch_root@.wf(),
    ensures
        out is Some ==> {
            let node = out.unwrap();
            &&& node.wf()
            &&& node@.wf()
            &&& node@ == crate::betree::LinkedBetree_v::BetreeNode::empty_root(
                crate::betree::Domain_v::total_domain(),
            ).extend_buffer_seq(crate::betree::LinkedSeq_v::LinkedSeq {
                addrs: seq![branch_root@],
            })
            &&& BetreeNodePageFmt::spec_new().marshallable(node.parsedv())
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(node)
            &&& BetreeNodePageFmt::spec_new().spec_size(node.parsedv())
                == PAGE_SIZE_BYTES
        },
{
    let fmt = BetreeNodePageFmt::new();
    let node = IBetreeNode {
        buffers: vec![branch_root],
        pivots: vec![IElement::Elem { e: 0 }, IElement::Max],
        children: vec![None],
        flushed: vec![0],
    };
    if node.buffers.len() > fmt.buffers_fmt.max_length
        || node.pivots.len() > fmt.pivots_fmt.max_length
        || node.children.len() > fmt.children_fmt.max_length
        || node.flushed.len() > fmt.flushed_fmt.max_length
        || node.buffers.len() > u8::MAX as usize
        || node.pivots.len() > u8::MAX as usize
        || node.children.len() > u8::MAX as usize
        || node.flushed.len() > u8::MAX as usize
    {
        return None;
    }
    proof {
        assert(node.wf());
        assert(node@.buffers.addrs == seq![branch_root@]);
        assert(node@.pivots.pivots
            == seq![crate::spec::KeyType_t::Element::Elem { e: 0 },
                crate::spec::KeyType_t::Element::Max]);
        assert(node@.children
            == seq![None::<crate::disk::GenericDisk_v::Address>]);
        assert(node@.flushed.offsets == seq![0nat]);



        assert(crate::betree::Domain_v::total_domain().wf());
        let expected = crate::betree::LinkedBetree_v::BetreeNode::empty_root(
            crate::betree::Domain_v::total_domain(),
        ).extend_buffer_seq(crate::betree::LinkedSeq_v::LinkedSeq {
            addrs: seq![branch_root@],
        });




        assert(expected.buffers.addrs == seq![branch_root@]);
        assert(expected.pivots.pivots
            == seq![crate::spec::KeyType_t::Element::Elem { e: 0 },
                crate::spec::KeyType_t::Element::Max]);
        assert(expected.children
            == seq![None::<crate::disk::GenericDisk_v::Address>]);
        assert(expected.flushed.offsets == seq![0nat]);
        assert(node@ == expected);
        assert(node@.wf());
        bounded_betree_node_marshallable(&node);
    }
    Some(node)
}

pub fn build_grow_betree_root(
    old_root: Option<IAddress>,
) -> (out: Option<IBetreeNode>)
    requires match old_root {
        Some(root) => root@.wf(),
        None => true,
    },
    ensures
        out is Some ==> {
            let node = out.unwrap();
            &&& node.wf()
            &&& node@.wf()
            &&& node@ == crate::betree::LinkedBetree_v::BetreeNode {
                buffers: crate::betree::LinkedSeq_v::LinkedSeq::empty(),
                pivots: crate::betree::PivotTable_v::domain_to_pivots(
                    crate::betree::Domain_v::total_domain(),
                ),
                children: seq![crate::implementation::IBranchNode_v::iopt_addr(
                    old_root,
                )],
                flushed: crate::betree::BufferOffsets_v::BufferOffsets {
                    offsets: seq![0nat],
                },
            }
            &&& BetreeNodePageFmt::spec_new().marshallable(node.parsedv())
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(node)
            &&& BetreeNodePageFmt::spec_new().spec_size(node.parsedv())
                == PAGE_SIZE_BYTES
        },
{
    let fmt = BetreeNodePageFmt::new();
    let node = IBetreeNode {
        buffers: Vec::new(),
        pivots: vec![IElement::Elem { e: 0 }, IElement::Max],
        children: vec![old_root],
        flushed: vec![0],
    };
    if node.buffers.len() > fmt.buffers_fmt.max_length
        || node.pivots.len() > fmt.pivots_fmt.max_length
        || node.children.len() > fmt.children_fmt.max_length
        || node.flushed.len() > fmt.flushed_fmt.max_length
        || node.buffers.len() > u8::MAX as usize
        || node.pivots.len() > u8::MAX as usize
        || node.children.len() > u8::MAX as usize
        || node.flushed.len() > u8::MAX as usize
    {
        return None;
    }
    proof {
        assert(node.wf());




        assert(node@.pivots.pivots
            == seq![crate::spec::KeyType_t::Element::Elem { e: 0 },
                crate::spec::KeyType_t::Element::Max]);
        let expected = crate::betree::LinkedBetree_v::BetreeNode {
            buffers: crate::betree::LinkedSeq_v::LinkedSeq::empty(),
            pivots: crate::betree::PivotTable_v::domain_to_pivots(
                crate::betree::Domain_v::total_domain(),
            ),
            children: seq![crate::implementation::IBranchNode_v::iopt_addr(
                old_root,
            )],
            flushed: crate::betree::BufferOffsets_v::BufferOffsets {
                offsets: seq![0nat],
            },
        };
        assert(expected.pivots.pivots
            == seq![crate::spec::KeyType_t::Element::Elem { e: 0 },
                crate::spec::KeyType_t::Element::Max]);
        assert(node@ == expected);
        assert(node@.wf());
        bounded_betree_node_marshallable(&node);
    }
    Some(node)
}

pub fn marshall_betree_node_page(node: &IBetreeNode) -> (out: Vec<u8>)
    requires
        node.wf(),
        BetreeNodePageFmt::spec_new().marshallable(node.parsedv()),
        BetreeNodePageFmt::spec_new().impl_marshallable(*node),
        BetreeNodePageFmt::spec_new().spec_size(node.parsedv())
            == PAGE_SIZE_BYTES,
    ensures
        out.len() == PAGE_SIZE_BYTES,
        BetreeNodePageFmt::spec_new().parsable(out@),
        raw_page_to_betree_node(out@) == node@,
{
    let fmt = BetreeNodePageFmt::new();
    let mut out = vec![0u8; PAGE_SIZE_BYTES];
    let end = fmt.exec_marshall(node, &mut out, 0);
    proof {
        assert(fmt == BetreeNodePageFmt::spec_new());
        assert(end == PAGE_SIZE_BYTES);
        assert(out@.subrange(0, end as int) == out@);
        assert(fmt.parsable(out@));
        assert(fmt.parse(out@) == node.parsedv());
        assert(raw_page_to_betree_node(out@) == node@);
    }
    out
}

} // verus!
