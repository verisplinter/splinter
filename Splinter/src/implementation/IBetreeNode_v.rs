// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::betree::BufferOffsets_v::BufferOffsets;
use crate::betree::LinkedBetree_v::BetreeNode;
use crate::betree::LinkedSeq_v::LinkedSeq;
use crate::betree::PivotTable_v::PivotTable;
use crate::disk::GenericDisk_v::{Address, Pointer};
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::IAddress;
use crate::spec::KeyType_t::Element;

verus! {

#[derive(Debug)]
pub enum IElement {
    Max,
    Elem { e: u64 },
}

impl Parsedview<Element> for IElement {
    open spec fn parsedv(&self) -> Element {
        match self {
            Self::Max => Element::Max,
            Self::Elem { e } => Element::Elem { e: *e },
        }
    }
}

impl View for IElement {
    type V = Element;

    open spec fn view(&self) -> Element {
        self.parsedv()
    }
}

impl WF for IElement { }

impl IElement {
    pub fn clone_checked(&self) -> (out: Self)
        ensures out@ == self@, out == *self,
    {
        match self {
            Self::Max => Self::Max,
            Self::Elem { e } => Self::Elem { e: *e },
        }
    }
}

fn clone_elements(elements: &Vec<IElement>) -> (out: Vec<IElement>)
    ensures Parsedview::<Seq<Element>>::parsedv(&out)
        == Parsedview::<Seq<Element>>::parsedv(elements),
{
    let mut out = Vec::<IElement>::new();
    let mut index = 0usize;
    while index < elements.len()
        invariant
            index <= elements.len(),
            Parsedview::<Seq<Element>>::parsedv(&out)
                == Parsedview::<Seq<Element>>::parsedv(elements)
                    .take(index as int),
        decreases elements.len() - index,
    {
        out.push(elements[index].clone_checked());
        proof {
            assert(Parsedview::<Seq<Element>>::parsedv(&out)
                == Parsedview::<Seq<Element>>::parsedv(elements)
                    .take(index as int + 1));
        }
        index += 1;
    }
    proof {
        assert(Parsedview::<Seq<Element>>::parsedv(elements)
            .take(index as int)
            == Parsedview::<Seq<Element>>::parsedv(elements));
    }
    out
}

#[derive(Debug)]
pub struct IBetreeNode {
    pub buffers: Vec<IAddress>,
    pub pivots: Vec<IElement>,
    pub children: Vec<Option<IAddress>>,
    pub flushed: Vec<u64>,
}

impl Parsedview<BetreeNode> for IBetreeNode {
    open spec fn parsedv(&self) -> BetreeNode {
        BetreeNode {
            buffers: LinkedSeq {
                addrs: Parsedview::<Seq<Address>>::parsedv(&self.buffers),
            },
            pivots: PivotTable {
                pivots: Parsedview::<Seq<Element>>::parsedv(&self.pivots),
            },
            children: Parsedview::<Seq<Pointer>>::parsedv(&self.children),
            flushed: BufferOffsets {
                offsets: Parsedview::<Seq<nat>>::parsedv(&self.flushed),
            },
        }
    }
}

impl View for IBetreeNode {
    type V = BetreeNode;

    open spec fn view(&self) -> BetreeNode {
        self.parsedv()
    }
}

impl IBetreeNode {
    pub fn clone_checked(&self) -> (out: Self)
        ensures
            out@ == self@,
            out.wf() == self.wf(),
    {
        let out = Self {
            buffers: self.buffers.clone(),
            pivots: clone_elements(&self.pivots),
            children: self.children.clone(),
            flushed: self.flushed.clone(),
        };
        proof {
            assert(out@ == self@);
            assert(out.wf() == self.wf());
        }
        out
    }
}

impl WF for IBetreeNode {
    open spec fn wf(&self) -> bool {
        &&& self.buffers.wf()
        &&& self.pivots.wf()
        &&& self.children.wf()
        &&& self.flushed.wf()
    }
}

} // verus!
