// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_seqs_equal;

use crate::betree::BufferOffsets_v::BufferOffsets;
use crate::betree::LinkedBetree_v::BetreeNode;
use crate::betree::LinkedSeq_v::LinkedSeq;
use crate::betree::PivotTable_v::PivotTable;
use crate::disk::GenericDisk_v::{Address, Pointer};
use crate::implementation::IBetreeNode_v::{IBetreeNode, IElement};
use crate::marshalling::IAddressFormat_v::IAddressFormat;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::NatFormat_v::NatFormat;
use crate::marshalling::OptionFormat_v::OptionFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformSizedMarshal_v::UniformSizedMarshal;
use crate::marshalling::WF_v::WF;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Element;
use crate::trusted::ClientAPI_t::BLOCK_SIZE;

verus! {

pub const BETREE_NODE_FORMAT_VERSION: u8 = 1;
// The four regions fill the remaining 999 bytes and admit 30 buffer roots,
// 27 pivots, 27 children, and 30 flushed offsets.
pub const BETREE_NODE_BUFFERS_SIZE: usize = 247;
pub const BETREE_NODE_PIVOTS_SIZE: usize = 252;
pub const BETREE_NODE_CHILDREN_SIZE: usize = 252;
pub const BETREE_NODE_FLUSHED_SIZE: usize = 248;

pub const BETREE_ELEMENT_ELEM_TAG: u8 = 0;
pub const BETREE_ELEMENT_MAX_TAG: u8 = 1;

pub struct IElementFormat {
    pub payload_fmt: IntFormat<u64>,
}

impl IElementFormat {
    pub open spec fn spec_new() -> Self {
        Self { payload_fmt: IntFormat::spec_new() }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        Self { payload_fmt: IntFormat::new() }
    }
}

impl UniformSized for IElementFormat {
    open spec fn us_valid(&self) -> bool {
        &&& self.payload_fmt.us_valid()
        &&& self.payload_fmt.uniform_size() + 1 <= usize::MAX
    }

    open spec fn uniform_size(&self) -> usize {
        (1 + self.payload_fmt.uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self) {
        self.payload_fmt.uniform_size_ensures();
    }

    exec fn exec_uniform_size(&self) -> (out: usize) {
        1 + self.payload_fmt.exec_uniform_size()
    }
}

impl Marshal for IElementFormat {
    type DV = Element;
    type U = IElement;

    open spec fn valid(&self) -> bool {
        &&& self.payload_fmt.valid()
        &&& self.us_valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        &&& data.len() >= self.uniform_size()
        &&& match data[0] {
            BETREE_ELEMENT_ELEM_TAG => self.payload_fmt.parsable(
                data.subrange(1, 1 + self.payload_fmt.uniform_size() as int),
            ),
            BETREE_ELEMENT_MAX_TAG => true,
            _ => false,
        }
    }

    open spec fn parse(&self, data: Seq<u8>) -> Element {
        match data[0] {
            BETREE_ELEMENT_ELEM_TAG => Element::Elem {
                e: self.payload_fmt.parse(
                    data.subrange(1, 1 + self.payload_fmt.uniform_size() as int),
                ) as u64,
            },
            BETREE_ELEMENT_MAX_TAG => Element::Max,
            _ => arbitrary(),
        }
    }

    open spec fn marshallable(&self, value: Element) -> bool {
        match value {
            Element::Elem { e } => self.payload_fmt.marshallable(e as int),
            Element::Max => true,
        }
    }

    open spec fn impl_marshallable(&self, value: IElement) -> bool {
        match value {
            IElement::Elem { e } => self.payload_fmt.impl_marshallable(e),
            IElement::Max => true,
        }
    }

    open spec fn spec_size(&self, _value: Element) -> usize {
        self.uniform_size()
    }

    exec fn exec_size(&self, _value: &IElement) -> (out: usize) {
        self.exec_uniform_size()
    }

    exec fn exec_marshall(
        &self,
        value: &IElement,
        data: &mut Vec<u8>,
        start: usize,
    ) -> (end: usize) {
        let end = start + self.exec_uniform_size();
        match value {
            IElement::Elem { e } => {
                data.set(start, BETREE_ELEMENT_ELEM_TAG);
                let payload_end = self.payload_fmt.exec_marshall(
                    e,
                    data,
                    start + 1,
                );
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    let body = subr.subrange(
                        1,
                        1 + self.payload_fmt.uniform_size() as int,
                    );
                    assert(payload_end == end);
                    assert(body == data@.subrange(
                        (start + 1) as int,
                        payload_end as int,
                    ));
                    assert(self.payload_fmt.parsable(body));
                    assert(Parsedview::<int>::parsedv(e) == *e as int);
                    assert(self.payload_fmt.parse(body) == *e as int);
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
            },
            IElement::Max => {
                data.set(start, BETREE_ELEMENT_MAX_TAG);
                proof {
                    let subr = data@.subrange(start as int, end as int);
                    assert(self.parsable(subr));
                    assert(self.parse(subr) == value.parsedv());
                }
            },
        }
        end
    }

    exec fn try_parse(
        &self,
        slice: &Slice,
        data: &Vec<u8>,
    ) -> (out: Option<IElement>) {
        if slice.len() < self.exec_uniform_size() {
            proof {
                assert(!self.parsable(slice@.i(data@)));
            }
            return None;
        }

        match data[slice.start] {
            BETREE_ELEMENT_ELEM_TAG => {
                let body = slice.subslice(
                    1,
                    1 + self.payload_fmt.exec_uniform_size(),
                );
                match self.payload_fmt.try_parse(&body, data) {
                    None => {
                        proof {
                            let idata = slice@.i(data@);
                            assert(body@.i(data@) == idata.subrange(
                                1,
                                1 + self.payload_fmt.uniform_size() as int,
                            ));
                            assert(!self.parsable(idata));
                        }
                        None
                    },
                    Some(e) => {
                        let out = IElement::Elem { e };
                        proof {
                            let idata = slice@.i(data@);
                            assert(body@.i(data@) == idata.subrange(
                                1,
                                1 + self.payload_fmt.uniform_size() as int,
                            ));
                            assert(self.parsable(idata));
                            assert(out.parsedv() == self.parse(idata));
                            assert(out.wf());
                        }
                        Some(out)
                    },
                }
            },
            BETREE_ELEMENT_MAX_TAG => {
                let out = IElement::Max;
                proof {
                    let idata = slice@.i(data@);
                    assert(self.parsable(idata));
                    assert(out.parsedv() == self.parse(idata));
                    assert(out.wf());
                }
                Some(out)
            },
            _ => {
                proof {
                    assert(!self.parsable(slice@.i(data@)));
                }
                None
            },
        }
    }
}

impl UniformSizedMarshal for IElementFormat {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        assert forall |value: Element|
            #[trigger] self.spec_size(value) == self.uniform_size() by { }
    }
}

pub type BetreeBuffersFormat =
    ResizableUniformSizedElementSeqFormat<IAddressFormat, u8>;
pub type BetreePivotsFormat =
    ResizableUniformSizedElementSeqFormat<IElementFormat, u8>;
pub type BetreeChildrenFormat =
    ResizableUniformSizedElementSeqFormat<OptionFormat<IAddressFormat>, u8>;
pub type BetreeFlushedFormat =
    ResizableUniformSizedElementSeqFormat<NatFormat<u64>, u8>;

pub open spec fn betree_node_from_parts(
    buffers: Seq<Address>,
    pivots: Seq<Element>,
    children: Seq<Pointer>,
    flushed: Seq<nat>,
) -> BetreeNode {
    BetreeNode {
        buffers: LinkedSeq { addrs: buffers },
        pivots: PivotTable { pivots },
        children,
        flushed: BufferOffsets { offsets: flushed },
    }
}

pub struct IBetreeNodeFormat {
    pub buffers_fmt: BetreeBuffersFormat,
    pub pivots_fmt: BetreePivotsFormat,
    pub children_fmt: BetreeChildrenFormat,
    pub flushed_fmt: BetreeFlushedFormat,
}

impl IBetreeNodeFormat {
    pub open spec fn spec_new() -> Self {
        Self {
            buffers_fmt: BetreeBuffersFormat::spec_new(
                IAddressFormat::spec_new(),
                IntFormat::<u8>::spec_new(),
                BETREE_NODE_BUFFERS_SIZE,
            ),
            pivots_fmt: BetreePivotsFormat::spec_new(
                IElementFormat::spec_new(),
                IntFormat::<u8>::spec_new(),
                BETREE_NODE_PIVOTS_SIZE,
            ),
            children_fmt: BetreeChildrenFormat::spec_new(
                OptionFormat::spec_new(IAddressFormat::spec_new()),
                IntFormat::<u8>::spec_new(),
                BETREE_NODE_CHILDREN_SIZE,
            ),
            flushed_fmt: BetreeFlushedFormat::spec_new(
                NatFormat::<u64>::spec_new(),
                IntFormat::<u8>::spec_new(),
                BETREE_NODE_FLUSHED_SIZE,
            ),
        }
    }

    pub fn new() -> (out: Self)
        ensures
            out == Self::spec_new(),
            out.valid(),
    {
        Self {
            buffers_fmt: BetreeBuffersFormat::new(
                IAddressFormat::new(),
                IntFormat::<u8>::new(),
                BETREE_NODE_BUFFERS_SIZE,
            ),
            pivots_fmt: BetreePivotsFormat::new(
                IElementFormat::new(),
                IntFormat::<u8>::new(),
                BETREE_NODE_PIVOTS_SIZE,
            ),
            children_fmt: BetreeChildrenFormat::new(
                OptionFormat::new(IAddressFormat::new()),
                IntFormat::<u8>::new(),
                BETREE_NODE_CHILDREN_SIZE,
            ),
            flushed_fmt: BetreeFlushedFormat::new(
                NatFormat::<u64>::new(),
                IntFormat::<u8>::new(),
                BETREE_NODE_FLUSHED_SIZE,
            ),
        }
    }

    pub open spec fn buffers_start(&self) -> int { 1 }
    pub open spec fn pivots_start(&self) -> int {
        self.buffers_start() + self.buffers_fmt.uniform_size() as int
    }
    pub open spec fn children_start(&self) -> int {
        self.pivots_start() + self.pivots_fmt.uniform_size() as int
    }
    pub open spec fn flushed_start(&self) -> int {
        self.children_start() + self.children_fmt.uniform_size() as int
    }

    pub open spec fn parsed_node(&self, data: Seq<u8>) -> BetreeNode {
        betree_node_from_parts(
            self.buffers_fmt.parse(data.subrange(
                self.buffers_start(),
                self.pivots_start(),
            )),
            self.pivots_fmt.parse(data.subrange(
                self.pivots_start(),
                self.children_start(),
            )),
            self.children_fmt.parse(data.subrange(
                self.children_start(),
                self.flushed_start(),
            )),
            self.flushed_fmt.parse(data.subrange(
                self.flushed_start(),
                self.uniform_size() as int,
            )),
        )
    }
}

impl UniformSized for IBetreeNodeFormat {
    open spec fn us_valid(&self) -> bool {
        &&& self.buffers_fmt.us_valid()
        &&& self.pivots_fmt.us_valid()
        &&& self.children_fmt.us_valid()
        &&& self.flushed_fmt.us_valid()
        &&& 1
            + self.buffers_fmt.uniform_size()
            + self.pivots_fmt.uniform_size()
            + self.children_fmt.uniform_size()
            + self.flushed_fmt.uniform_size()
            == BLOCK_SIZE
    }

    open spec fn uniform_size(&self) -> usize {
        (1
            + self.buffers_fmt.uniform_size()
            + self.pivots_fmt.uniform_size()
            + self.children_fmt.uniform_size()
            + self.flushed_fmt.uniform_size()) as usize
    }

    proof fn uniform_size_ensures(&self) { }

    exec fn exec_uniform_size(&self) -> (out: usize) {
        1
            + self.buffers_fmt.exec_uniform_size()
            + self.pivots_fmt.exec_uniform_size()
            + self.children_fmt.exec_uniform_size()
            + self.flushed_fmt.exec_uniform_size()
    }
}

impl Marshal for IBetreeNodeFormat {
    type DV = BetreeNode;
    type U = IBetreeNode;

    open spec fn valid(&self) -> bool {
        &&& self.us_valid()
        &&& self.buffers_fmt.valid()
        &&& self.pivots_fmt.valid()
        &&& self.children_fmt.valid()
        &&& self.flushed_fmt.valid()
    }

    open spec fn parsable(&self, data: Seq<u8>) -> bool {
        &&& data.len() >= self.uniform_size()
        &&& data[0] == BETREE_NODE_FORMAT_VERSION
        &&& self.buffers_fmt.parsable(data.subrange(
            self.buffers_start(),
            self.pivots_start(),
        ))
        &&& self.pivots_fmt.parsable(data.subrange(
            self.pivots_start(),
            self.children_start(),
        ))
        &&& self.children_fmt.parsable(data.subrange(
            self.children_start(),
            self.flushed_start(),
        ))
        &&& self.flushed_fmt.parsable(data.subrange(
            self.flushed_start(),
            self.uniform_size() as int,
        ))
    }

    open spec fn parse(&self, data: Seq<u8>) -> BetreeNode {
        self.parsed_node(data)
    }

    open spec fn marshallable(&self, value: BetreeNode) -> bool {
        &&& value.wf()
        &&& self.buffers_fmt.marshallable(value.buffers.addrs)
        &&& self.pivots_fmt.marshallable(value.pivots.pivots)
        &&& self.children_fmt.marshallable(value.children)
        &&& self.flushed_fmt.marshallable(value.flushed.offsets)
    }

    open spec fn impl_marshallable(&self, value: IBetreeNode) -> bool {
        &&& value.wf()
        &&& self.buffers_fmt.impl_marshallable(value.buffers)
        &&& self.pivots_fmt.impl_marshallable(value.pivots)
        &&& self.children_fmt.impl_marshallable(value.children)
        &&& self.flushed_fmt.impl_marshallable(value.flushed)
    }

    open spec fn spec_size(&self, _value: BetreeNode) -> usize {
        self.uniform_size()
    }

    exec fn exec_size(&self, _value: &IBetreeNode) -> (out: usize) {
        self.exec_uniform_size()
    }

    exec fn exec_marshall(
        &self,
        value: &IBetreeNode,
        data: &mut Vec<u8>,
        start: usize,
    ) -> (end: usize) {
        data.set(start, BETREE_NODE_FORMAT_VERSION);
        let buffers_end = self.buffers_fmt.exec_marshall(
            &value.buffers,
            data,
            start + 1,
        );
        let ghost buffers_data = data@.subrange(
            (start + 1) as int,
            buffers_end as int,
        );
        let pivots_end = self.pivots_fmt.exec_marshall(
            &value.pivots,
            data,
            buffers_end,
        );
        let ghost pivots_data = data@.subrange(
            buffers_end as int,
            pivots_end as int,
        );
        let children_end = self.children_fmt.exec_marshall(
            &value.children,
            data,
            pivots_end,
        );
        let ghost children_data = data@.subrange(
            pivots_end as int,
            children_end as int,
        );
        let end = self.flushed_fmt.exec_marshall(
            &value.flushed,
            data,
            children_end,
        );
        let ghost flushed_data = data@.subrange(
            children_end as int,
            end as int,
        );
        proof {
            let subr = data@.subrange(start as int, end as int);
            assert(end == start + self.uniform_size());
            assert(subr[0] == BETREE_NODE_FORMAT_VERSION);
            assert_seqs_equal!(
                subr.subrange(self.buffers_start(), self.pivots_start()),
                buffers_data,
                idx => { }
            );
            assert_seqs_equal!(
                subr.subrange(self.pivots_start(), self.children_start()),
                pivots_data,
                idx => { }
            );
            assert_seqs_equal!(
                subr.subrange(self.children_start(), self.flushed_start()),
                children_data,
                idx => { }
            );
            assert_seqs_equal!(
                subr.subrange(
                    self.flushed_start(),
                    self.uniform_size() as int,
                ),
                flushed_data,
                idx => { }
            );
            assert(self.buffers_fmt.parsable(buffers_data));
            assert(self.pivots_fmt.parsable(pivots_data));
            assert(self.children_fmt.parsable(children_data));
            assert(self.flushed_fmt.parsable(flushed_data));
            assert(self.buffers_fmt.parse(buffers_data)
                == Parsedview::<Seq<Address>>::parsedv(&value.buffers));
            assert(self.pivots_fmt.parse(pivots_data)
                == Parsedview::<Seq<Element>>::parsedv(&value.pivots));
            assert(self.children_fmt.parse(children_data)
                == Parsedview::<Seq<Pointer>>::parsedv(&value.children));
            assert(self.flushed_fmt.parse(flushed_data)
                == Parsedview::<Seq<nat>>::parsedv(&value.flushed));
            assert(self.parsed_node(subr) == value.parsedv());
            assert(self.parsable(subr));
            assert(self.parse(subr) == value.parsedv());
        }
        end
    }

    exec fn try_parse(
        &self,
        slice: &Slice,
        data: &Vec<u8>,
    ) -> (out: Option<IBetreeNode>) {
        let total_size = self.exec_uniform_size();
        if slice.len() < total_size {
            proof {
                assert(!self.parsable(slice@.i(data@)));
            }
            return None;
        }
        if data[slice.start] != BETREE_NODE_FORMAT_VERSION {
            proof {
                assert(!self.parsable(slice@.i(data@)));
            }
            return None;
        }

        let buffers_start = 1;
        let pivots_start = buffers_start + self.buffers_fmt.exec_uniform_size();
        let children_start = pivots_start + self.pivots_fmt.exec_uniform_size();
        let flushed_start = children_start + self.children_fmt.exec_uniform_size();

        let buffers_slice = slice.subslice(buffers_start, pivots_start);
        let buffers = match self.buffers_fmt.try_parse(&buffers_slice, data) {
            None => {
                proof {
                    let idata = slice@.i(data@);
                    assert(buffers_slice@.i(data@) == idata.subrange(
                        self.buffers_start(),
                        self.pivots_start(),
                    ));
                    assert(!self.parsable(idata));
                }
                return None;
            },
            Some(value) => value,
        };

        let pivots_slice = slice.subslice(pivots_start, children_start);
        let pivots = match self.pivots_fmt.try_parse(&pivots_slice, data) {
            None => {
                proof {
                    let idata = slice@.i(data@);
                    assert(pivots_slice@.i(data@) == idata.subrange(
                        self.pivots_start(),
                        self.children_start(),
                    ));
                    assert(!self.parsable(idata));
                }
                return None;
            },
            Some(value) => value,
        };

        let children_slice = slice.subslice(children_start, flushed_start);
        let children = match self.children_fmt.try_parse(&children_slice, data) {
            None => {
                proof {
                    let idata = slice@.i(data@);
                    assert(children_slice@.i(data@) == idata.subrange(
                        self.children_start(),
                        self.flushed_start(),
                    ));
                    assert(!self.parsable(idata));
                }
                return None;
            },
            Some(value) => value,
        };

        let flushed_slice = slice.subslice(flushed_start, total_size);
        let flushed = match self.flushed_fmt.try_parse(&flushed_slice, data) {
            None => {
                proof {
                    let idata = slice@.i(data@);
                    assert(flushed_slice@.i(data@) == idata.subrange(
                        self.flushed_start(),
                        self.uniform_size() as int,
                    ));
                    assert(!self.parsable(idata));
                }
                return None;
            },
            Some(value) => value,
        };

        let node = IBetreeNode {
            buffers,
            pivots,
            children,
            flushed,
        };

        proof {
            let idata = slice@.i(data@);
            assert(buffers_slice@.i(data@) == idata.subrange(
                self.buffers_start(),
                self.pivots_start(),
            ));
            assert(pivots_slice@.i(data@) == idata.subrange(
                self.pivots_start(),
                self.children_start(),
            ));
            assert(children_slice@.i(data@) == idata.subrange(
                self.children_start(),
                self.flushed_start(),
            ));
            assert(flushed_slice@.i(data@) == idata.subrange(
                self.flushed_start(),
                self.uniform_size() as int,
            ));
            assert(node.parsedv() == self.parsed_node(idata));
            assert(self.parsable(idata));
            assert(node.parsedv() == self.parse(idata));
            assert(node.buffers.wf());
            assert(node.pivots.wf());
            assert(node.children.wf());
            assert(node.flushed.wf());
            assert(node.wf());
        }
        Some(node)
    }
}

impl UniformSizedMarshal for IBetreeNodeFormat {
    proof fn uniform_size_matches_spec_size(self: &Self) {
        assert forall |value: BetreeNode|
            #[trigger] self.spec_size(value) == self.uniform_size() by { }
    }
}

pub type BetreeNodePageFmt = IBetreeNodeFormat;

pub open spec fn raw_page_to_betree_node(raw_page: RawPage) -> BetreeNode {
    let fmt = IBetreeNodeFormat::spec_new();
    if fmt.parsable(raw_page) {
        fmt.parse(raw_page)
    } else {
        arbitrary()
    }
}

} // verus!
