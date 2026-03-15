// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;

use crate::allocation_layer::AllocationBranch_v::{BranchNode as AllocationBranchNode, Summary};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::{IAddress, IAU};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

#[derive(Debug)]
pub enum IBranchNode {
    Leaf { keys: Vec<Key>, msgs: Vec<Message> },
    Index { pivots: Vec<Key>, children: Vec<IAddress>, aux_ptr: Option<IAddress> },
    Auxiliary { summary_aus: Vec<IAU> },
}

#[verifier::ext_equal]
pub enum BranchNodeImage {
    Leaf { keys: Seq<Key>, msgs: Seq<Message> },
    Index { pivots: Seq<Key>, children: Seq<Address>, aux_ptr: Pointer },
    Auxiliary { summary_aus: Seq<AU> },
}

pub open spec fn iopt_addr(ptr: Option<IAddress>) -> Pointer
{
    match ptr {
        Some(addr) => Some(addr@),
        None => None,
    }
}

pub open spec fn iaddr_seq(addrs: Seq<IAddress>) -> Seq<Address>
{
    addrs.map(|i: int, addr: IAddress| addr@)
}

pub open spec fn iau_seq(aus: Seq<IAU>) -> Seq<AU>
{
    aus.map(|i: int, au: IAU| au as nat)
}

pub open spec fn iau_seq_set(aus: Seq<IAU>) -> Summary
{
    Map::new(|i: int| 0 <= i < aus.len(), |i: int| aus[i] as nat).values()
}

pub open spec fn branch_node_image(node: AllocationBranchNode) -> BranchNodeImage
{
    match node {
        AllocationBranchNode::Leaf { keys, msgs } => BranchNodeImage::Leaf { keys, msgs },
        AllocationBranchNode::Index { pivots, children, aux_ptr } => BranchNodeImage::Index {
            pivots,
            children,
            aux_ptr,
        },
        AllocationBranchNode::Auxiliary(summary_aus) => BranchNodeImage::Auxiliary {
            summary_aus: summary_aus.to_seq(),
        },
    }
}

impl Parsedview<BranchNodeImage> for IBranchNode {
    open spec fn parsedv(&self) -> BranchNodeImage
    {
        match self {
            Self::Leaf { keys, msgs } => BranchNodeImage::Leaf { keys: keys@, msgs: msgs@ },
            Self::Index { pivots, children, aux_ptr } => BranchNodeImage::Index {
                pivots: pivots@,
                children: iaddr_seq(children@),
                aux_ptr: iopt_addr(*aux_ptr),
            },
            Self::Auxiliary { summary_aus } => BranchNodeImage::Auxiliary {
                summary_aus: iau_seq(summary_aus@),
            },
        }
    }
}

impl View for BranchNodeImage {
    type V = AllocationBranchNode;

    open spec fn view(&self) -> Self::V
    {
        if self is Leaf {
            AllocationBranchNode::Leaf { keys: self->keys, msgs: self->msgs }
        } else if self is Index {
            AllocationBranchNode::Index {
                pivots: self->pivots,
                children: self->children,
                aux_ptr: self->aux_ptr,
            }
        } else {
            AllocationBranchNode::Auxiliary(self->summary_aus.to_set())
        }
    }
}

impl View for IBranchNode {
    type V = AllocationBranchNode;

    open spec fn view(&self) -> Self::V
    {
        self.parsedv().view()
    }
}

impl Clone for IBranchNode {
    fn clone(&self) -> Self {
        match self {
            Self::Leaf { keys, msgs } => Self::Leaf { keys: keys.clone(), msgs: msgs.clone() },
            Self::Index { pivots, children, aux_ptr } => Self::Index {
                pivots: pivots.clone(),
                children: children.clone(),
                aux_ptr: *aux_ptr,
            },
            Self::Auxiliary { summary_aus } => Self::Auxiliary { summary_aus: summary_aus.clone() },
        }
    }
}

impl WF for IBranchNode {
    open spec fn wf(&self) -> bool
    {
        match self {
            Self::Leaf { keys, msgs } => {
                &&& keys.wf()
                &&& msgs.wf()
                &&& keys.len() == msgs.len()
            }
            Self::Index { pivots, children, aux_ptr } => {
                &&& pivots.wf()
                &&& children.wf()
                &&& aux_ptr.wf()
                &&& children.len() == pivots.len() + 1
            }
            Self::Auxiliary { summary_aus } => summary_aus.wf(),
        }
    }
}

} // verus!
