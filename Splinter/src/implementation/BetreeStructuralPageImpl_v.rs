// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_seqs_equal;

use crate::betree::SplitRequest_v::SplitRequest;
use crate::implementation::BetreePageImpl_v::bounded_betree_node_marshallable;
use crate::implementation::BetreeQueryImpl_v::betree_route_index;
use crate::implementation::FracCacheImpl_v::PAGE_SIZE_BYTES;
use crate::implementation::IBetreeNode_v::{IBetreeNode, IElement};
use crate::marshalling::IBetreeNodeFormat_v::BetreeNodePageFmt;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::{Element, Key};

verus! {

pub enum IBetreeSplitRequest {
    Leaf { child_idx: usize, split_key: Key },
    Index { child_idx: usize, child_pivot_idx: usize },
}

impl IBetreeSplitRequest {
    pub open spec fn i(&self) -> SplitRequest {
        match self {
            Self::Leaf { child_idx, split_key } => SplitRequest::SplitLeaf {
                child_idx: *child_idx as nat,
                split_key: *split_key,
            },
            Self::Index { child_idx, child_pivot_idx } => {
                SplitRequest::SplitIndex {
                    child_idx: *child_idx as nat,
                    child_pivot_idx: *child_pivot_idx as nat,
                }
            },
        }
    }

    pub fn child_idx(&self) -> (out: usize)
        ensures out as nat == self.i().get_child_idx(),
    {
        match self {
            Self::Leaf { child_idx, .. }
            | Self::Index { child_idx, .. } => *child_idx,
        }
    }

    pub fn valid_for_child(
        &self,
        child: &IBetreeNode,
    ) -> (out: bool)
        requires
            child.wf(),
            child@.wf(),
        ensures
            out ==> match self.i() {
                SplitRequest::SplitLeaf { split_key, .. } => {
                    child@.can_split_leaf(split_key)
                },
                SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                    child@.can_split_index(child_pivot_idx)
                },
            },
    {
        match self {
            Self::Leaf { split_key, .. } => {
                if child.children.len() != 1
                    || child.children[0].is_some()
                    || child.flushed.len() != 1
                    || child.flushed[0] != 0
                {
                    return false;
                }
                let start_lt = match &child.pivots[0] {
                    IElement::Elem { e } => *e < split_key.0,
                    IElement::Max => false,
                };
                let below_end = match &child.pivots[child.pivots.len() - 1] {
                    IElement::Elem { e } => split_key.0 < *e,
                    IElement::Max => true,
                };
                proof {
                    if start_lt && below_end {
                        assert(child@.children.len() == 1);
                        assert(child@.children[0] is None);
                        assert(child@.flushed.offsets == seq![0nat]);
                        assert(child@.is_leaf());
                        assert(child@.pivots.pivots[0]
                            == child.pivots[0]@);
                        assert(child@.pivots.pivots.last()
                            == child.pivots[child.pivots.len() - 1]@);
                        match &child.pivots[0] {
                            IElement::Elem { e } => {
                                assert(*e < split_key.0);
                            },
                            IElement::Max => {
                                assert(false);
                            },
                        }
                        match &child.pivots[child.pivots.len() - 1] {
                            IElement::Elem { e } => {
                                assert(split_key.0 < *e);
                            },
                            IElement::Max => {},
                        }
                        assert(child@.my_domain().contains(*split_key));
                        assert(child@.my_domain()->start
                            != crate::spec::KeyType_t::to_element(*split_key));
                        assert(child@.can_split_leaf(*split_key));
                    }
                }
                start_lt && below_end
            },
            Self::Index { child_pivot_idx, .. } => {
                let mut index = 0usize;
                while index < child.children.len()
                    invariant
                        index <= child.children.len(),
                        forall |i: int| 0 <= i < index
                            ==> (#[trigger] child.children@[i]) is Some,
                    decreases child.children.len() - index,
                {
                    if child.children[index].is_none() {
                        return false;
                    }
                    index += 1;
                }
                proof {
                    assert forall |i: nat| child@.valid_child_index(i)
                        implies (#[trigger] child@.children[i as int]) is Some by {
                        assert(i < child.children.len());
                        assert(child.children@[i as int] is Some);
                    }
                    assert(child@.is_index());
                    assert(child@.pivots.num_ranges()
                        == child.children.len() as int);
                }
                let out = 0 < *child_pivot_idx
                    && *child_pivot_idx < child.children.len();
                proof {
                    if out {
                        assert(child@.can_split_index(
                            *child_pivot_idx as nat,
                        ));
                    }
                }
                out
            },
        }
    }
}

fn clone_element_range(
    values: &Vec<IElement>,
    start: usize,
    end: usize,
) -> (out: Vec<IElement>)
    requires start <= end <= values.len(),
    ensures
        Parsedview::<Seq<Element>>::parsedv(&out)
            == Parsedview::<Seq<Element>>::parsedv(values)
                .subrange(start as int, end as int),
{
    let mut out = Vec::<IElement>::new();
    let mut index = start;
    while index < end
        invariant
            start <= index <= end,
            end <= values.len(),
            Parsedview::<Seq<Element>>::parsedv(&out)
                == Parsedview::<Seq<Element>>::parsedv(values)
                    .subrange(start as int, index as int),
        decreases end - index,
    {
        out.push(values[index].clone_checked());
        index += 1;
    }
    out
}

fn clone_pointer_range(
    values: &Vec<Option<IAddress>>,
    start: usize,
    end: usize,
) -> (out: Vec<Option<IAddress>>)
    requires start <= end <= values.len(),
    ensures
        Parsedview::<Seq<crate::disk::GenericDisk_v::Pointer>>::parsedv(&out)
            == Parsedview::<Seq<crate::disk::GenericDisk_v::Pointer>>::parsedv(
                values,
            ).subrange(start as int, end as int),
{
    let mut out = Vec::<Option<IAddress>>::new();
    let mut index = start;
    while index < end
        invariant
            start <= index <= end,
            end <= values.len(),
            Parsedview::<Seq<crate::disk::GenericDisk_v::Pointer>>::parsedv(
                &out,
            ) == Parsedview::<Seq<crate::disk::GenericDisk_v::Pointer>>::parsedv(
                values,
            ).subrange(start as int, index as int),
        decreases end - index,
    {
        out.push(values[index]);
        index += 1;
    }
    out
}

fn clone_offset_range(
    values: &Vec<u64>,
    start: usize,
    end: usize,
) -> (out: Vec<u64>)
    requires start <= end <= values.len(),
    ensures
        Parsedview::<Seq<nat>>::parsedv(&out)
            == Parsedview::<Seq<nat>>::parsedv(values)
                .subrange(start as int, end as int),
{
    let mut out = Vec::<u64>::new();
    let mut index = start;
    while index < end
        invariant
            start <= index <= end,
            end <= values.len(),
            Parsedview::<Seq<nat>>::parsedv(&out)
                == Parsedview::<Seq<nat>>::parsedv(values)
                    .subrange(start as int, index as int),
        decreases end - index,
    {
        out.push(values[index]);
        index += 1;
    }
    out
}

fn clone_address_range(
    values: &Vec<IAddress>,
    start: usize,
    end: usize,
) -> (out: Vec<IAddress>)
    requires start <= end <= values.len(),
    ensures
        Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(&out)
            == Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                values,
            ).subrange(start as int, end as int),
{
    let mut out = Vec::<IAddress>::new();
    let mut index = start;
    while index < end
        invariant
            start <= index <= end,
            end <= values.len(),
            Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                &out,
            ) == Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                values,
            ).subrange(start as int, index as int),
        decreases end - index,
    {
        out.push(values[index]);
        index += 1;
    }
    out
}

fn append_address_range(
    out: &mut Vec<IAddress>,
    values: &Vec<IAddress>,
    start: usize,
    end: usize,
)
    requires
        start <= end <= values.len(),
    ensures
        Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(out)
            == Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                old(out),
            ) + Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                values,
            ).subrange(start as int, end as int),
{
    let ghost initial = out@;
    let mut index = start;
    while index < end
        invariant
            start <= index <= end,
            end <= values.len(),
            out@ == initial + values@.subrange(start as int, index as int),
        decreases end - index,
    {
        out.push(values[index]);
        index += 1;
    }
    proof {
        assert(values@.subrange(start as int, index as int)
            == values@.subrange(start as int, end as int));
        assert_seqs_equal!(
            Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(out),
            Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                old(out),
            ) + Parsedview::<Seq<crate::disk::GenericDisk_v::Address>>::parsedv(
                values,
            ).subrange(start as int, end as int),
            i => {
                if i < initial.len() {
                    assert(out@[i] == initial[i]);
                } else {
                    let j = i - initial.len();
                    assert(out@[i] == values@[start as int + j]);
                }
            }
        );
    }
}

pub open spec fn betree_node_fits_page(node: &IBetreeNode) -> bool {
    &&& node.buffers@.len()
        <= BetreeNodePageFmt::spec_new().buffers_fmt.max_length
    &&& node.pivots@.len()
        <= BetreeNodePageFmt::spec_new().pivots_fmt.max_length
    &&& node.children@.len()
        <= BetreeNodePageFmt::spec_new().children_fmt.max_length
    &&& node.flushed@.len()
        <= BetreeNodePageFmt::spec_new().flushed_fmt.max_length
    &&& node.buffers@.len() <= u8::MAX as int
    &&& node.pivots@.len() <= u8::MAX as int
    &&& node.children@.len() <= u8::MAX as int
    &&& node.flushed@.len() <= u8::MAX as int
}

fn node_fits_page(node: &IBetreeNode) -> (out: bool)
    ensures out == betree_node_fits_page(node),
{
    let fmt = BetreeNodePageFmt::new();
    node.buffers.len() <= fmt.buffers_fmt.max_length
        && node.pivots.len() <= fmt.pivots_fmt.max_length
        && node.children.len() <= fmt.children_fmt.max_length
        && node.flushed.len() <= fmt.flushed_fmt.max_length
        && node.buffers.len() <= u8::MAX as usize
        && node.pivots.len() <= u8::MAX as usize
        && node.children.len() <= u8::MAX as usize
        && node.flushed.len() <= u8::MAX as usize
}

pub struct SplitNodePages {
    pub left: IBetreeNode,
    pub right: IBetreeNode,
    pub parent: IBetreeNode,
}

pub struct FlushNodePages {
    pub parent: IBetreeNode,
    pub child: IBetreeNode,
}

pub struct CompactNodePage {
    pub node: IBetreeNode,
}

pub open spec fn compact_node_view(
    node: crate::betree::LinkedBetree_v::BetreeNode,
    start: nat,
    end: nat,
    sealed_root: crate::disk::GenericDisk_v::Address,
) -> crate::betree::LinkedBetree_v::BetreeNode
    recommends start < end <= node.buffers.len(),
{
    crate::betree::LinkedBetree_v::BetreeNode {
        buffers: node.buffers.update_subrange(
            start as int,
            end as int,
            sealed_root,
        ),
        flushed: node.flushed.adjust_compact(start as int, end as int),
        ..node
    }
}

pub fn build_compact_node_page(
    source: &IBetreeNode,
    start: usize,
    end: usize,
    sealed_root: IAddress,
) -> (out: Option<CompactNodePage>)
    requires
        source.wf(),
        source@.wf(),
        (start as nat) < (end as nat),
        end as nat <= source@.buffers.len(),
        sealed_root@.wf(),
        compact_node_view(
            source@,
            start as nat,
            end as nat,
            sealed_root@,
        ).wf(),
    ensures
        out is Some ==> {
            let page = out.unwrap();
            &&& page.node.wf()
            &&& page.node@.wf()
            &&& page.node@ == compact_node_view(
                source@,
                start as nat,
                end as nat,
                sealed_root@,
            )
            &&& BetreeNodePageFmt::spec_new().marshallable(page.node@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(page.node)
            &&& BetreeNodePageFmt::spec_new().spec_size(page.node@)
                == PAGE_SIZE_BYTES
        },
{
    let mut node = source.clone_checked();
    let mut buffers = clone_address_range(&source.buffers, 0, start);
    buffers.push(sealed_root);
    append_address_range(&mut buffers, &source.buffers, end, source.buffers.len());
    node.buffers = buffers;

    let mut flushed = Vec::<u64>::new();
    let mut index = 0usize;
    while index < source.flushed.len()
        invariant
            index <= source.flushed.len(),
            flushed@.len() == index,
            flushed@ == Seq::<u64>::new(index as nat, |i: int| {
                let old = source.flushed@[i];
                if old <= start as u64 {
                    old
                } else if old < end as u64 {
                    start as u64
                } else {
                    (old - (end - start) as u64 + 1) as u64
                }
            }),
        decreases source.flushed.len() - index,
    {
        let old = source.flushed[index];
        let next = if old <= start as u64 {
            old
        } else if old < end as u64 {
            start as u64
        } else {
            old - (end - start) as u64 + 1u64
        };
        flushed.push(next);
        index += 1;
    }
    node.flushed = flushed;

    proof {
        assert(node@ == compact_node_view(
            source@,
            start as nat,
            end as nat,
            sealed_root@,
        )) by {


            assert_seqs_equal!(
                node@.flushed.offsets,
                source@.flushed.adjust_compact(
                    start as int,
                    end as int,
                ).offsets,
                i => {}
            );
        }
        assert(node.wf());
        assert(node@.wf());
    }
    if !node_fits_page(&node) {
        return None;
    }
    proof { bounded_betree_node_marshallable(&node); }
    Some(CompactNodePage { node })
}

pub open spec fn flush_child_view(
    parent: crate::betree::LinkedBetree_v::BetreeNode,
    child: crate::betree::LinkedBetree_v::BetreeNode,
    child_idx: nat,
) -> crate::betree::LinkedBetree_v::BetreeNode
    recommends
        parent.valid_child_index(child_idx),
{
    let flushed_ofs = parent.flushed.offsets[child_idx as int];
    child.extend_buffer_seq(parent.buffers.slice(
        flushed_ofs as int,
        parent.buffers.len() as int,
    ))
}

pub open spec fn flush_parent_view(
    parent: crate::betree::LinkedBetree_v::BetreeNode,
    child_idx: nat,
    buffer_gc: nat,
    new_child_addr: crate::disk::GenericDisk_v::Address,
) -> crate::betree::LinkedBetree_v::BetreeNode
    recommends
        parent.valid_child_index(child_idx),
        buffer_gc <= parent.buffers.len(),
        parent.flushed.update(child_idx as int, parent.buffers.len())
            .all_gte(buffer_gc),
{
    let flush_upto = parent.buffers.len();
    crate::betree::LinkedBetree_v::BetreeNode {
        buffers: parent.buffers.slice(buffer_gc as int, flush_upto as int),
        children: parent.children.update(
            child_idx as int,
            Some(new_child_addr),
        ),
        flushed: parent.flushed.update(
            child_idx as int,
            flush_upto,
        ).shift_left(buffer_gc),
        ..parent
    }
}

pub fn build_flush_node_pages(
    parent: &IBetreeNode,
    child: &IBetreeNode,
    child_idx: usize,
    buffer_gc: usize,
    new_child_addr: IAddress,
) -> (out: Option<FlushNodePages>)
    requires
        parent.wf(),
        child.wf(),
        parent@.wf(),
        child@.wf(),
        parent@.valid_child_index(child_idx as nat),
        parent@.children[child_idx as int] is Some,
        buffer_gc as nat <= parent@.buffers.len(),
        parent@.flushed.update(
            child_idx as int,
            parent@.buffers.len(),
        ).all_gte(buffer_gc as nat),
        flush_parent_view(
            parent@,
            child_idx as nat,
            buffer_gc as nat,
            new_child_addr@,
        ).wf(),
        flush_child_view(parent@, child@, child_idx as nat).wf(),
        new_child_addr@.wf(),
    ensures
        out is Some ==> {
            let pages = out.unwrap();
            &&& pages.parent@ == flush_parent_view(
                parent@,
                child_idx as nat,
                buffer_gc as nat,
                new_child_addr@,
            )
            &&& pages.child@ == flush_child_view(
                parent@,
                child@,
                child_idx as nat,
            )
            &&& pages.parent.wf() && pages.parent@.wf()
            &&& pages.child.wf() && pages.child@.wf()
            &&& BetreeNodePageFmt::spec_new().marshallable(pages.parent@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(pages.parent)
            &&& BetreeNodePageFmt::spec_new().marshallable(pages.child@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(pages.child)
            &&& BetreeNodePageFmt::spec_new().spec_size(pages.parent@)
                == PAGE_SIZE_BYTES
            &&& BetreeNodePageFmt::spec_new().spec_size(pages.child@)
                == PAGE_SIZE_BYTES
        },
{
    let flush_upto = parent.buffers.len();
    let flushed_ofs = parent.flushed[child_idx] as usize;
    if flushed_ofs > flush_upto || buffer_gc > flush_upto {
        proof { assert(false); }
        return None;
    }

    let mut new_child = child.clone_checked();
    append_address_range(
        &mut new_child.buffers,
        &parent.buffers,
        flushed_ofs,
        flush_upto,
    );

    let mut new_parent = parent.clone_checked();
    new_parent.buffers = clone_address_range(
        &parent.buffers,
        buffer_gc,
        flush_upto,
    );
    new_parent.children.set(child_idx, Some(new_child_addr));
    let mut shifted = Vec::<u64>::new();
    let mut index = 0usize;
    while index < parent.flushed.len()
        invariant
            index <= parent.flushed.len(),
            shifted@.len() == index,
            shifted@ == Seq::<u64>::new(index as nat, |i: int| {
                let source = if i == child_idx as int {
                    flush_upto as u64
                } else {
                    parent.flushed@[i]
                };
                (source - buffer_gc as u64) as u64
            }),
        decreases parent.flushed.len() - index,
    {
        let source = if index == child_idx {
            flush_upto as u64
        } else {
            parent.flushed[index]
        };
        proof {
            let ghost updated = parent@.flushed.update(
                child_idx as int,
                parent@.buffers.len(),
            );
            assert(updated.all_gte(buffer_gc as nat));
            assert(updated.offsets[index as int] >= buffer_gc as nat);
            assert(source as nat == updated.offsets[index as int]);
            assert(source as nat >= buffer_gc as nat);
        }
        if source < buffer_gc as u64 {
            proof { assert(false); }
            return None;
        }
        let ghost shifted_before = shifted@;
        shifted.push(source - buffer_gc as u64);
        proof {
            assert((source - buffer_gc as u64) as nat
                == source as nat - buffer_gc as nat);
            assert_seqs_equal!(
                shifted@,
                Seq::<u64>::new(index as nat + 1, |i: int| {
                    let model_source = if i == child_idx as int {
                        flush_upto as u64
                    } else {
                        parent.flushed@[i]
                    };
                    (model_source - buffer_gc as u64) as u64
                }),
                i => {
                    if i < index as int {
                        assert(shifted@[i] == shifted_before[i]);
                    } else {
                        assert(i == index as int);
                        assert(shifted@[i] == source - buffer_gc as u64);
                    }
                }
            );
        }
        index += 1;
    }
    new_parent.flushed = shifted;

    proof {
        assert(new_child@ == flush_child_view(
            parent@,
            child@,
            child_idx as nat,
        )) by {


        }
        assert(new_parent@ == flush_parent_view(
            parent@,
            child_idx as nat,
            buffer_gc as nat,
            new_child_addr@,
        )) by {



            assert_seqs_equal!(
                new_parent@.flushed.offsets,
                parent@.flushed.update(
                    child_idx as int,
                    parent@.buffers.len(),
                ).shift_left(buffer_gc as nat).offsets,
                i => {}
            );
        }
        assert(new_parent.wf());
        assert(new_child.wf());
        assert(new_parent@.wf());
        assert(new_child@.wf());
    }
    if !node_fits_page(&new_parent) || !node_fits_page(&new_child) {
        return None;
    }
    proof {
        bounded_betree_node_marshallable(&new_parent);
        bounded_betree_node_marshallable(&new_child);
    }
    Some(FlushNodePages { parent: new_parent, child: new_child })
}

pub open spec fn split_parent_view(
    parent: crate::betree::LinkedBetree_v::BetreeNode,
    child: crate::betree::LinkedBetree_v::BetreeNode,
    request: SplitRequest,
    left: crate::disk::GenericDisk_v::Address,
    right: crate::disk::GenericDisk_v::Address,
) -> crate::betree::LinkedBetree_v::BetreeNode {
    let child_idx = request.get_child_idx();
    let pivot = match request {
        SplitRequest::SplitLeaf { split_key, .. } => {
            crate::spec::KeyType_t::to_element(split_key)
        },
        SplitRequest::SplitIndex { child_pivot_idx, .. } => {
            child.pivots[child_pivot_idx as int]
        },
    };
    crate::betree::LinkedBetree_v::BetreeNode {
        pivots: parent.pivots.insert(child_idx as int + 1, pivot),
        children: parent.children.update(
            child_idx as int,
            Some(left),
        ).insert(child_idx as int + 1, Some(right)),
        flushed: parent.flushed.dup(child_idx as int),
        ..parent
    }
}

pub fn build_split_node_pages(
    parent: &IBetreeNode,
    child: &IBetreeNode,
    request: &IBetreeSplitRequest,
    left_addr: IAddress,
    right_addr: IAddress,
) -> (out: Option<SplitNodePages>)
    requires
        parent.wf(),
        child.wf(),
        parent@.wf(),
        parent@.valid_child_index(request.i().get_child_idx()),
        parent@.children[request.i().get_child_idx() as int] is Some,
        match request.i() {
            SplitRequest::SplitLeaf { split_key, .. } => {
                child@.can_split_leaf(split_key)
            },
            SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                child@.can_split_index(child_pivot_idx)
            },
        },
        left_addr@.wf(),
        right_addr@.wf(),
        split_parent_view(
            parent@,
            child@,
            request.i(),
            left_addr@,
            right_addr@,
        ).wf(),
    ensures
        out is Some ==> {
            let pages = out.unwrap();
            let request_view = request.i();
            let child_idx = request_view.get_child_idx();
            let pair = match request_view {
                SplitRequest::SplitLeaf { split_key, .. } => {
                    child@.split_leaf(split_key)
                },
                SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                    child@.split_index(child_pivot_idx)
                },
            };
            let pivot = match request_view {
                SplitRequest::SplitLeaf { split_key, .. } => {
                    crate::spec::KeyType_t::to_element(split_key)
                },
                SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                    child@.pivots[child_pivot_idx as int]
                },
            };
            &&& pages.left@ == pair.0
            &&& pages.right@ == pair.1
            &&& pages.parent@ == split_parent_view(
                parent@,
                child@,
                request_view,
                left_addr@,
                right_addr@,
            )
            &&& pages.left.wf() && pages.left@.wf()
            &&& pages.right.wf() && pages.right@.wf()
            &&& pages.parent.wf() && pages.parent@.wf()
            &&& BetreeNodePageFmt::spec_new().marshallable(pages.left@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(pages.left)
            &&& BetreeNodePageFmt::spec_new().marshallable(pages.right@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(pages.right)
            &&& BetreeNodePageFmt::spec_new().marshallable(pages.parent@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(pages.parent)
            &&& BetreeNodePageFmt::spec_new().spec_size(pages.left@)
                == PAGE_SIZE_BYTES
            &&& BetreeNodePageFmt::spec_new().spec_size(pages.right@)
                == PAGE_SIZE_BYTES
            &&& BetreeNodePageFmt::spec_new().spec_size(pages.parent@)
                == PAGE_SIZE_BYTES
        },
{
    let child_idx = request.child_idx();
    let (left, right, pivot) = match request {
        IBetreeSplitRequest::Leaf { split_key, .. } => {
            let mut left = child.clone_checked();
            let mut right = child.clone_checked();
            left.pivots.set(1, IElement::Elem { e: split_key.0 });
            right.pivots.set(0, IElement::Elem { e: split_key.0 });
            (left, right, IElement::Elem { e: split_key.0 })
        },
        IBetreeSplitRequest::Index { child_pivot_idx, .. } => {
            let left = IBetreeNode {
                buffers: child.buffers.clone(),
                pivots: clone_element_range(
                    &child.pivots,
                    0,
                    *child_pivot_idx + 1,
                ),
                children: clone_pointer_range(
                    &child.children,
                    0,
                    *child_pivot_idx,
                ),
                flushed: clone_offset_range(
                    &child.flushed,
                    0,
                    *child_pivot_idx,
                ),
            };
            let right = IBetreeNode {
                buffers: child.buffers.clone(),
                pivots: clone_element_range(
                    &child.pivots,
                    *child_pivot_idx,
                    child.pivots.len(),
                ),
                children: clone_pointer_range(
                    &child.children,
                    *child_pivot_idx,
                    child.children.len(),
                ),
                flushed: clone_offset_range(
                    &child.flushed,
                    *child_pivot_idx,
                    child.flushed.len(),
                ),
            };
            let pivot = child.pivots[*child_pivot_idx].clone_checked();
            (left, right, pivot)
        },
    };
    let ghost pivot_view = pivot@;
    proof {
        assert(pivot_view == match request.i() {
            SplitRequest::SplitLeaf { split_key, .. } => {
                crate::spec::KeyType_t::to_element(split_key)
            },
            SplitRequest::SplitIndex { child_pivot_idx, .. } => {
                child@.pivots[child_pivot_idx as int]
            },
        });
    }
    let mut new_parent = parent.clone_checked();
    new_parent.children.set(child_idx, Some(left_addr));
    new_parent.children.insert(child_idx + 1, Some(right_addr));
    new_parent.pivots.insert(child_idx + 1, pivot);
    let flushed = new_parent.flushed[child_idx];
    new_parent.flushed.insert(child_idx + 1, flushed);

    proof {







        match request {
            IBetreeSplitRequest::Leaf { split_key, .. } => {
                assert(left@.pivots.pivots
                    == child@.pivots.pivots.update(
                        1,
                        crate::spec::KeyType_t::to_element(*split_key),
                    ));
                assert(right@.pivots.pivots
                    == child@.pivots.pivots.update(
                        0,
                        crate::spec::KeyType_t::to_element(*split_key),
                    ));
                assert(left@ == child@.split_leaf(*split_key).0);
                assert(right@ == child@.split_leaf(*split_key).1);
            },
            IBetreeSplitRequest::Index { child_pivot_idx, .. } => {
                assert(left@.pivots.pivots
                    == child@.pivots.pivots.subrange(
                        0,
                        *child_pivot_idx as int + 1,
                    ));
                assert(right@.pivots.pivots
                    == child@.pivots.pivots.subrange(
                        *child_pivot_idx as int,
                        child@.pivots.pivots.len() as int,
                    ));
                assert(left@ == child@.split_index(*child_pivot_idx as nat).0);
                assert(right@ == child@.split_index(*child_pivot_idx as nat).1);
            },
        }
        assert(new_parent@.pivots.pivots
            == parent@.pivots.pivots.insert(
                child_idx as int + 1,
                pivot_view,
            ));
        assert(left.wf());
        assert(right.wf());
        assert(new_parent.wf());
        assert(left@.wf());
        assert(right@.wf());
        assert(new_parent@ == split_parent_view(
            parent@,
            child@,
            request.i(),
            left_addr@,
            right_addr@,
        ));
        assert(new_parent@.wf());
    }
    if !node_fits_page(&left)
        || !node_fits_page(&right)
        || !node_fits_page(&new_parent)
    {
        return None;
    }
    proof {
        bounded_betree_node_marshallable(&left);
        bounded_betree_node_marshallable(&right);
        bounded_betree_node_marshallable(&new_parent);
    }
    Some(SplitNodePages { left, right, parent: new_parent })
}

pub fn build_ancestor_replacement(
    source: &IBetreeNode,
    key: Key,
    child_root: IAddress,
) -> (out: Option<IBetreeNode>)
    requires
        source.wf(),
        source@.key_in_domain(key),
        child_root@.wf(),
    ensures
        out is Some ==> {
            let node = out.unwrap();
            let route = source@.pivots.route(key);
            &&& node@ == crate::betree::LinkedBetree_v::BetreeNode {
                children: source@.children.update(
                    route,
                    Some(child_root@),
                ),
                ..source@
            }
            &&& node.wf()
            &&& node@.wf()
            &&& BetreeNodePageFmt::spec_new().marshallable(node@)
            &&& BetreeNodePageFmt::spec_new().impl_marshallable(node)
            &&& BetreeNodePageFmt::spec_new().spec_size(node@)
                == PAGE_SIZE_BYTES
        },
{
    proof {
        assert(source@.wf());
        assert(source@.pivots.wf());
        crate::spec::KeyType_t::Element::strictly_sorted_implies_sorted(
            source@.pivots.pivots,
        );
    }
    let route = betree_route_index(&source.pivots, key);
    proof {
        source@.pivots.route_lemma(key);
        assert(0 <= source@.pivots.route(key)
            < source@.pivots.num_ranges());
        assert(source@.children.len() == source@.pivots.num_ranges());
        assert(route as int == source@.pivots.route(key));
        assert(route < source.children.len());
    }
    let mut node = source.clone_checked();
    node.children.set(route, Some(child_root));
    proof {
        assert(route as int == source@.pivots.route(key));
        assert(node@.children == source@.children.update(
            source@.pivots.route(key),
            Some(child_root@),
        ));
        assert(node@ == crate::betree::LinkedBetree_v::BetreeNode {
            children: source@.children.update(
                source@.pivots.route(key),
                Some(child_root@),
            ),
            ..source@
        });
        assert(node.wf());
        assert(node@.wf());
    }
    if !node_fits_page(&node) {
        return None;
    }
    proof {
        bounded_betree_node_marshallable(&node);
    }
    Some(node)
}

} // verus!
