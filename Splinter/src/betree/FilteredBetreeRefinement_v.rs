// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::prelude::*;
//use vstd::prelude_macros::*;
use vstd::prelude::*;
use crate::spec::KeyType_t::{Element, Key, to_element};
use crate::spec::Messages_t::{Message, nop_delta};
use crate::abstract_system::StampedMap_v::{Stamped, empty};
use crate::betree::Domain_v::{Domain, total_domain};
use crate::betree::PivotTable_v::PivotTable;
use crate::betree::Buffer_v::{Buffer, SimpleBuffer};
use crate::betree::BufferSeq_v::BufferSeq;
use crate::betree::PivotBetree_v;
use crate::betree::PivotBetree_v::PivotBetree;
use crate::betree::FilteredBetree_v::{BetreeNode, FilteredBetree, Path, QueryReceipt, QueryReceiptLine, StampedBetree};
use crate::betree::SplitRequest_v::SplitRequest;

verus! {

broadcast use PivotTable::route_lemma; 

impl BetreeNode {
    pub open spec(checked) fn i_buffer(self) -> SimpleBuffer
        recommends self.wf(), self is Node
    {
        let offset_map = self.make_offset_map();
        self->buffers.i_filtered(offset_map)
    }

    pub open spec /*XXX(checked)*/ fn i_children_seq(self, start: int) -> Seq<PivotBetree_v::BetreeNode>
        recommends self is Node, 0 <= start <= self->children.len()
        decreases self, 0nat, self->children.len()-start 
        when self is Node && 0 <= start <= self->children.len()
    {
        if start == self->children.len() {
            seq![]
        } else {
            //XXX need to instantiate linked_children
            let child = self->children[start].i();
            seq![child] + self.i_children_seq(start+1)
        }
    }

    pub open spec(checked) fn i_children(self) -> Seq<PivotBetree_v::BetreeNode>
        recommends self is Node
        decreases self, 1nat
    {
        self.i_children_seq(0)
    }

    pub open spec(checked) fn i(self) -> PivotBetree_v::BetreeNode
        recommends self.wf()
        decreases self
    {
        if self is Nil {
            PivotBetree_v::BetreeNode::Nil{}
        } else {
            PivotBetree_v::BetreeNode::Node{
                pivots: self->pivots,
                buffer: self.i_buffer(), 
                children: self.i_children()
            }
        }
    }

    proof fn i_children_seq_lemma(self, start: int)
        requires self.wf(), self is Node, 0 <= start <= self->children.len()
        ensures self.i_children_seq(start).len() == self->children.len() - start,
            forall |i: int| 0 <= i < self.i_children_seq(start).len() 
            ==> {
                &&& (#[trigger] self.i_children_seq(start)[i]).wf()
                &&& self.i_children_seq(start)[i] == self->children[i+start].i()
            }
        decreases self, 0nat, self->children.len()-start 
    {
        if start < self->children.len() {
            let result = self.i_children_seq(start);
            let child = self->children[start];
            let sub_seq = self.i_children_seq(start+1);
            assert(self.valid_child_index(start as nat));

            child.i_wf();
            self.i_children_seq_lemma(start+1);
        }
    }

    proof fn i_children_lemma(self)
        requires self is Node, self.wf()
        ensures 
            self.i().wf_children(),
            self->children.len() == self.i()->children.len(),
            forall |i| (#[trigger] self.valid_child_index(i))
                ==> self.i()->children[i as int] == self->children[i as int].i()
        decreases self, 1nat
    {
        self.i_children_seq_lemma(0);
    }

    broadcast proof fn i_wf(self)
        requires self.wf()
        ensures (#[trigger]self.i()).wf(), self is Node ==> self.my_domain() == self.i().my_domain()
        decreases self, 2nat
    {
        if self is Node {
            self.i_children_lemma();
            assert(self.wf_children()); // trigger
   
            assert forall |i|
            (
                (#[trigger] self.i().valid_child_index(i))
                && self.i()->children[i as int] is Node
                && self.i()->children[i as int].local_structure() 
            ) implies {
                self.i()->children[i as int].my_domain() == self.child_domain(i)
            } by {
                assert(self.valid_child_index(i)); // trigger
            }
        }
    }

    #[verifier::opaque]
    closed spec(checked) fn is_active_key(self, k: Key) -> bool 
        recommends self.wf(), self is Node
    {
        exists |idx| self->buffers.key_in_buffer_filtered(self.make_offset_map(), 0, k, idx)
    }

    proof fn instantiate_buffer_idx_for_active_key(self, k: Key) -> (idx: int)
        requires 
            self.wf(), 
            self is Node,
            self.is_active_key(k)
        ensures 
            self->buffers.key_in_buffer_filtered(self.make_offset_map(), 0, k, idx)
    {
        reveal(BetreeNode::is_active_key);
        let idx = choose |idx| #[trigger] self->buffers.key_in_buffer_filtered(self.make_offset_map(), 0, k, idx);
        idx
    }

    proof fn key_in_buffer_implies_active_key(self, k: Key, idx: int)
        requires 
            self.wf(), 
            self is Node,
            self->buffers.key_in_buffer_filtered(self.make_offset_map(), 0, k, idx)
        ensures 
            self.is_active_key(k)
    {
        reveal(BetreeNode::is_active_key);
    }

    proof fn i_buffer_domain(self)
        requires self.wf(), self is Node
        ensures 
            forall |k| #[trigger] self.i_buffer().map.contains_key(k) ==> self.key_in_domain(k),
            forall |k| #[trigger] self.i_buffer().map.contains_key(k) <==> self.is_active_key(k)
    {
        reveal(BetreeNode::is_active_key);
        self->buffers.i_filtered_from_domain(self.make_offset_map(), 0);
    }

    broadcast proof fn query_from_refines(self, key: Key)
        requires self.wf(), self is Node, #[trigger] self.key_in_domain(key),
        ensures self->buffers.query_from(key, self.flushed_ofs(key) as int) == self.i()->buffer.query(key)
    {
        let offset_map = self.make_offset_map();
        self->buffers.query_from_same_as_i_filtered(key, 0, offset_map);
    }

    pub open spec /*XXX(checked)*/ fn children_have_matching_domains(self, other_children: Seq<BetreeNode>) -> bool
        recommends self.wf(), self.is_index()
    {
        &&& other_children.len() == self->children.len()
        &&& (forall |i| (#[trigger] self.valid_child_index(i)) ==> {
            &&& other_children[i as int].wf()
            &&& other_children[i as int] is Node
            //XXX need to instantiate linked_children
            &&& other_children[i as int].my_domain() == self->children[i as int].my_domain()
        })
    }

    proof fn i_preserves_children(self, other: Self, start: int, end: int)
        requires  
            self.wf(),
            other.wf(), 
            self is Node,
            other is Node,
            0 <= start <= end <= self->children.len(),
            self->children.subrange(start, end) =~= other->children,
        ensures
            self.i()->children.subrange(start, end) =~= other.i()->children
    {
        let children_subset = self.i()->children.subrange(start, end);

        self.i_children_lemma();
        other.i_children_lemma();

        assert forall |i| 0 <= i < other.i()->children.len()
        implies #[trigger] children_subset[i] =~= other.i()->children[i]
        by {
            assert(other.valid_child_index(i as nat)); // trigger
            assert(self.valid_child_index((i+start) as nat)); // trigger
        }
    }

    proof fn child_domain_implies_key_in_domain(self, child_idx: nat)
        requires self.wf(), self is Node, child_idx < self->children.len() 
        ensures forall |k: Key| #[trigger] self.child_domain(child_idx).contains(k) ==> self.key_in_domain(k)
    {
        let child_domain = self.child_domain(child_idx);
        assert forall |k: Key| #[trigger] child_domain.contains(k)
        implies self.key_in_domain(k)
        by {
            if self->pivots.num_ranges() == 1 {
            } else {
                if child_idx == 0 {
                    assert(Element::lt(child_domain->end, self.my_domain()->end)); // trigger
                } else if child_idx + 1 == self->pivots.num_ranges() {
                    assert(Element::lt(self.my_domain()->start, child_domain->start)); // trigger
                } else {
                    assert(Element::lt(child_domain->end, self.my_domain()->end)); // trigger
                }
            }
        }
    }

    proof fn extend_buffer_seq_wf(self, buffers: BufferSeq)
        requires self.wf(), self is Node
        ensures self.extend_buffer_seq(buffers).wf()
    {
        let result = self.extend_buffer_seq(buffers);
        assert forall |i| #[trigger] result.valid_child_index(i) implies self.valid_child_index(i) by {}
    }

    proof fn extend_buffer_seq_refines_merge_buffer(self, buffers: BufferSeq)
        requires self.wf(), self is Node
        ensures self.extend_buffer_seq(buffers).i() == self.i().merge_buffer(buffers.i().apply_filter(self.my_domain().key_set()))
    {
        let filter = self.my_domain().key_set();
        let a = self.extend_buffer_seq(buffers);
        self.extend_buffer_seq_wf(buffers);

        let b = self.i().merge_buffer(buffers.i().apply_filter(filter));

        // seems like we need a better lemma?
        // as long as children are the same 

        a.i_children_lemma();
        self.i_children_lemma();
        assert(a.i()->children =~= self.i()->children) by {
            assert forall |i| 0 <= i < a.i()->children.len()
            implies a.i()->children[i] =~= self.i()->children[i]
            by {
                assert(a.valid_child_index(i as nat)); // trigger
                assert(self.valid_child_index(i as nat)); // trigger
            }
        }

        let offset_map = self.make_offset_map();
        let a_offset_map = a.make_offset_map();

        self.i_buffer_domain();
        a.i_buffer_domain();

        assert forall |k| 
        ({
            &&& a.i()->buffer.map.contains_key(k) <==> #[trigger] b->buffer.map.contains_key(k)
            &&& a.i()->buffer.map.contains_key(k) ==> a.i()->buffer.map[k] == b->buffer.map[k]
        }) by {
            buffers.i_from_domain(0);

            if a.i()->buffer.map.contains_key(k) {
                let idx = a.instantiate_buffer_idx_for_active_key(k);
                if idx < self->buffers.len() {
                    self.key_in_buffer_implies_active_key(k, idx);
                } else {
                    let buffer_idx = idx-self->buffers.len();
                    assert(buffers.key_in_buffer(0, k, buffer_idx)); // trigger
                }

                assert(a.i()->buffer.map[k] == b->buffer.map[k]) by {
                    a.query_from_refines(k);
                    self.query_from_refines(k);
                    buffers.query_agrees_with_i(k, 0);
                    BufferSeq::extend_buffer_seq_query_ensures(buffers, 
                        self->buffers, k, offset_map.offsets[k] as int);
                }
            }

            if b->buffer.map.contains_key(k) {
                if buffers.i().apply_filter(filter).map.contains_key(k) {
                    let buffer_idx = choose |buffer_idx| buffers.key_in_buffer(0, k, buffer_idx);
                    let idx = buffer_idx + self->buffers.len();

                    a.key_in_buffer_implies_active_key(k, idx);
                } else {
                    let idx = self.instantiate_buffer_idx_for_active_key(k);
                    a.key_in_buffer_implies_active_key(k, idx);
                }
            }
        }
    }

    proof fn promote_commutes_with_i(self, domain: Domain)
        requires self.wf(), domain.wf(), domain is Domain
        ensures self.promote(domain).i() == self.i().promote(domain)
    {
        broadcast use BetreeNode::i_wf;

        // NOTE(JL): can't do just the following line:
        // assert(self.promote(domain).i() =~= self.i().promote(domain));
    }

    pub open spec(checked) fn split_element(self, request: SplitRequest) -> Element
        recommends self.can_split_parent(request)
    {
        let child = self->children[request.get_child_idx() as int];
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => child->pivots.pivots[child_pivot_idx as int]
        }
    }

    proof fn split_leaf_wf(self, split_key: Key)
        requires self.can_split_leaf(split_key)
        ensures self.split_leaf(split_key).0.wf(), self.split_leaf(split_key).1.wf()
    {
        assert(self.split_leaf(split_key).0.wf_children()); // trigger
        assert(self.split_leaf(split_key).1.wf_children()); // trigger
    }

    proof fn split_index_wf(self, pivot_idx: nat)
        requires self.can_split_index(pivot_idx)
        ensures 
            self.split_index(pivot_idx).0.wf(), 
            self.split_index(pivot_idx).1.wf(),
    {
        let (new_left, new_right) = self.split_index(pivot_idx);
        assert forall |i| new_left.valid_child_index(i) implies self.valid_child_index(i) by {}
        assert forall |i| new_right.valid_child_index(i) implies self.valid_child_index(i+pivot_idx) by {}
    }

    proof fn split_parent_wf(self, request: SplitRequest) 
        requires self.can_split_parent(request)
        ensures self.split_parent(request).wf()
    { 
        let child_idx = request.get_child_idx();
        let old_child = self->children[child_idx as int];
        let new_parent = self.split_parent(request);

        self->pivots.insert_wf(child_idx as int + 1, self.split_element(request));

        assert forall |i| #[trigger] new_parent.valid_child_index(i) implies 
        ({
            &&& i < child_idx ==> self.valid_child_index(i) 
            &&& i > child_idx + 1 ==> self.valid_child_index((i-1) as nat)
        }) by {}

        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => old_child.split_leaf_wf(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => old_child.split_index_wf(child_pivot_idx),
        }
    }

    pub closed spec fn shared_keys_same_active_range(self, other: Self) -> bool 
        recommends self.wf(), other.wf()
    {
        forall |k| other.key_in_domain(k) && self.key_in_domain(k)
            ==> other.flushed_ofs(k) == self.flushed_ofs(k)
    }

    proof fn sub_domain_equiv_apply_filter(self, other: Self)
        requires 
            self.wf(), 
            other.wf(),
            self is Node,
            other is Node,
            self->buffers == other->buffers,
            self.my_domain().includes(other.my_domain()),
            self.shared_keys_same_active_range(other),
        ensures
            other.i()->buffer =~= self.i()->buffer.apply_filter(other.my_domain().key_set())
    {
        let self_map = self.i()->buffer.apply_filter(other.my_domain().key_set()).map;
        let other_map = other.i()->buffer.map;

        other.i_buffer_domain();
        self.i_buffer_domain();

        assert forall |k| #[trigger] other_map.contains_key(k)
        implies {
            &&& self_map.contains_key(k)
            &&& other_map[k] == self_map[k]
        } by {
            let idx = other.instantiate_buffer_idx_for_active_key(k);
            self.key_in_buffer_implies_active_key(k, idx);
            broadcast use BetreeNode::query_from_refines;
        }

        assert forall |k| #[trigger] self_map.contains_key(k)
        implies other_map.contains_key(k)
        by {
            let idx = self.instantiate_buffer_idx_for_active_key(k);
            other.key_in_buffer_implies_active_key(k, idx);
        }

    }

    proof fn split_leaf_commutes_with_i(self, split_key: Key)
        requires self.can_split_leaf(split_key)
        ensures 
            self.split_leaf(split_key).0.wf(),
            self.split_leaf(split_key).1.wf(),
            self.split_leaf(split_key).0.i() == self.i().split_leaf(split_key).0,
            self.split_leaf(split_key).1.i() == self.i().split_leaf(split_key).1,
    {
        broadcast use BetreeNode::i_wf;
        
        let (left, right) = self.split_leaf(split_key);
        let (i_left, i_right) = self.i().split_leaf(split_key);
        self.split_leaf_wf(split_key);


        self.sub_domain_equiv_apply_filter(left);
        self.sub_domain_equiv_apply_filter(right);
    }
    
    proof fn split_index_commutes_with_i(self, pivot_idx: nat)
        requires self.can_split_index(pivot_idx)
        ensures
            self.split_index(pivot_idx).0.wf(),
            self.split_index(pivot_idx).1.wf(),
            self.split_index(pivot_idx).0.i() == self.i().split_index(pivot_idx).0,
            self.split_index(pivot_idx).1.i() == self.i().split_index(pivot_idx).1,
    {
        broadcast use BetreeNode::i_wf;
        broadcast use PivotTable::route_is_lemma;

        let (left, right) = self.split_index(pivot_idx);
        let (i_left, i_right) = self.i().split_index(pivot_idx);
        self.split_index_wf(pivot_idx);

        self.i_preserves_children(left, 0, left->children.len() as int);
        self.i_preserves_children(right, left->children.len() as int, self->children.len() as int);
    
        Element::strictly_sorted_implies_sorted(self->pivots.pivots);
        self.sub_domain_equiv_apply_filter(left);
        self.sub_domain_equiv_apply_filter(right);
    }

    proof fn split_parent_buffers_commutes_with_i(self, request: SplitRequest)
        requires 
            self.can_split_parent(request), 
            self.i().can_split_parent(request),
        ensures 
            self.split_parent(request).wf(),
            self.i().split_parent(request)->buffer == self.split_parent(request).i()->buffer
    {
        self.split_parent_wf(request);
        self.i().split_parent_wf(request);
        broadcast use BetreeNode::i_wf;

        let new_parent = self.split_parent(request);
        let i_new_parent = self.i().split_parent(request);
        let split_child_idx = request.get_child_idx() as int;

        assert forall |k| self.key_in_domain(k)
        implies self.flushed_ofs(k) == new_parent.flushed_ofs(k)
        by {
            let r = self->pivots.route(k);
            let e = to_element(k);

            if r < split_child_idx {
                new_parent->pivots.route_is_lemma(k, r);
            } else if r == split_child_idx {
                if Element::lt(e, new_parent->pivots.pivots[r+1]) {
                    new_parent->pivots.route_is_lemma(k, r);
                } else {
                    new_parent->pivots.route_is_lemma(k, r+1);
                }
            } else {
                new_parent->pivots.route_is_lemma(k, r+1);
            }
        }

        self.i_buffer_domain();
        new_parent.i_buffer_domain();
        self.sub_domain_equiv_apply_filter(new_parent);
    }

    proof fn split_parent_commutes_with_i(self, request: SplitRequest)
        requires self.can_split_parent(request)
        ensures 
            self.split_parent(request).wf(),
            self.i().can_split_parent(request),
            self.i().split_parent(request) == self.split_parent(request).i()
    {
        self.split_parent_wf(request);
        broadcast use BetreeNode::i_wf;

        let split_child_idx = request.get_child_idx() as int;
        let child = self->children[split_child_idx];
        let i_child = self.i()->children[split_child_idx];

        self.i_children_lemma();
        child.i_children_lemma();

        if request is SplitLeaf {
            assert(child.i_children() == i_child->children); // trigger
            child.split_leaf_commutes_with_i(request->split_key);
        } else {
            assert(forall |i| #[trigger] i_child.valid_child_index(i) ==> child.valid_child_index(i)); // trigger
            child.split_index_commutes_with_i(request->child_pivot_idx);
        }

        let split_parent = self.split_parent(request);
        let i_split_parent = self.i().split_parent(request);
        split_parent.i_children_lemma();

        assert forall |i| 0 <= i < split_parent.i()->children.len()
        implies #[trigger] split_parent.i()->children[i] =~= i_split_parent->children[i]
        by {
            assert(split_parent.valid_child_index(i as nat)); // trigger
            if i < split_child_idx + 1 {
                assert(self.valid_child_index(i as nat)); // trigger
            } else {
                assert(self.valid_child_index((i-1) as nat)); // trigger
            }
        }
        assert(split_parent.i()->children =~= i_split_parent->children); // trigger
        self.split_parent_buffers_commutes_with_i(request);
    }

    proof fn flush_wf(self, child_idx: nat, buffer_gc: nat)
        requires self.can_flush(child_idx, buffer_gc)
        ensures self.flush(child_idx, buffer_gc).wf()
    {
        let result = self.flush(child_idx, buffer_gc);
        let idx = child_idx as int;
        let flush_upto = self->buffers.len(); 

        let updated_flushed = self->flushed.update(idx, flush_upto);
        assert(updated_flushed.offsets[idx] == flush_upto); // trigger
        updated_flushed.shift_left_preserves_lte(buffer_gc, flush_upto);

        let flushed_ofs = self->flushed.offsets[idx];
        let buffers_to_child = self->buffers.slice(flushed_ofs as int, flush_upto as int);

        let child = self->children[idx];
        let child_domain = self.child_domain(child_idx);
        let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

        assert(child.wf()); // trigger
        child.promote(child_domain).extend_buffer_seq_wf(buffers_to_child);
        assert forall |i| #[trigger] result.valid_child_index(i) implies self.valid_child_index(i) by {}
    }

    proof fn active_slice_equiv_apply_filter(self, child_idx: nat)
        requires 
            self.wf(), 
            self is Node,
            self.valid_child_index(child_idx),
        ensures
            ({
                let flushed_ofs = self->flushed.offsets[child_idx as int] as int;
                let active_slice = self->buffers.slice(flushed_ofs, self->buffers.len() as int);
                &&& active_slice.i().apply_filter(self.child_domain(child_idx).key_set()) 
                    =~= self.i()->buffer.apply_filter(self.child_domain(child_idx).key_set())
            })
    {
        let flushed_ofs = self->flushed.offsets[child_idx as int] as int;
        let active_slice = self->buffers.slice(flushed_ofs, self->buffers.len() as int);
        let child_domain = self.child_domain(child_idx);
        let ofs_map = self.make_offset_map();

        self.i_buffer_domain();

        assert forall |k| #[trigger] child_domain.contains(k)
        implies ({
            &&& active_slice.i().map.contains_key(k) <==> self.i_buffer().map.contains_key(k)
            &&& active_slice.i().query(k) == self.i_buffer().query(k)
        }) by {
            self->pivots.route_is_lemma(k, child_idx as int);
            assert(self.flushed_ofs(k) == flushed_ofs);

            if active_slice.i().map.contains_key(k) {
                active_slice.i_from_domain(0);
                let buffer_idx = choose |buffer_idx| active_slice.key_in_buffer(0, k, buffer_idx);
                self.key_in_buffer_implies_active_key(k, buffer_idx+flushed_ofs);
                assert(self.i_buffer().map.contains_key(k));
            }

            if self.i_buffer().map.contains_key(k) {
                let buffer_idx = self.instantiate_buffer_idx_for_active_key(k);
                active_slice.i_from_domain(0);
                assert(active_slice.key_in_buffer(0, k, buffer_idx-flushed_ofs));
                assert(active_slice.i().map.contains_key(k));
            }

            active_slice.query_agrees_with_i(k, 0);
            assert(active_slice.query(k) == active_slice.i().query(k));

            self.query_from_refines(k);
            assert(self.i_buffer().query(k) == self->buffers.query_from(k, flushed_ofs as int));
            BufferSeq::common_buffer_seqs(active_slice, self->buffers, 0, flushed_ofs as int, k);
        }
    }

    proof fn flush_commutes_with_i(self, child_idx: nat, buffer_gc: nat)
        requires self.can_flush(child_idx, buffer_gc)
        ensures self.flush(child_idx, buffer_gc).i() == self.i().flush(child_idx)
    {
        self.flush_wf(child_idx, buffer_gc);
        broadcast use BetreeNode::i_wf;
        
        let flush_upto = self->buffers.len();
        let flushed_ofs = self->flushed.offsets[child_idx as int];
        let buffers_to_child = self->buffers.slice(flushed_ofs as int, flush_upto as int);

        let flushed = self.flush(child_idx, buffer_gc);
        let i_flushed = self.i().flush(child_idx);

        let child = self->children[child_idx as int];
        let child_domain = self.child_domain(child_idx);
        let new_child = child.promote(child_domain).extend_buffer_seq(buffers_to_child);

        assert forall |i| 0 <= i < flushed.i()->children.len()
        implies #[trigger] flushed.i()->children[i] =~= i_flushed->children[i]
        by {
            self.i_children_lemma();
            flushed.i_children_lemma();

            assert(self.valid_child_index(i as nat)); // trigger
            assert(flushed.valid_child_index(i as nat)); // trigger

            if i == child_idx {
                child.promote_commutes_with_i(child_domain);
                child.promote(child_domain).extend_buffer_seq_refines_merge_buffer(buffers_to_child);
                self.active_slice_equiv_apply_filter(child_idx);
            }
        }
        assert(flushed.i()->children =~= i_flushed->children); // trigger

        assert forall |k|
        ({
            &&& #[trigger] flushed.i()->buffer.map.contains_key(k) 
                <==> i_flushed->buffer.map.contains_key(k)
            &&& flushed.i()->buffer.map.contains_key(k) ==> 
                flushed.i()->buffer.map[k] == i_flushed->buffer.map[k]
        }) by {
            flushed.i_buffer_domain();
            self.i_buffer_domain();

            if i_flushed->buffer.map.contains_key(k) {
                assert(flushed.flushed_ofs(k) == self.flushed_ofs(k) - buffer_gc); // trigger
                let idx = self.instantiate_buffer_idx_for_active_key(k);
                flushed.key_in_buffer_implies_active_key(k, idx - buffer_gc);
            }

            if flushed.i()->buffer.map.contains_key(k) {
                if child_domain.contains(k) {
                    flushed->pivots.route_is_lemma(k, child_idx as int);
                }
                let idx = flushed.instantiate_buffer_idx_for_active_key(k);
                self.key_in_buffer_implies_active_key(k, idx + buffer_gc);

                self.query_from_refines(k);
                flushed.query_from_refines(k);
                BufferSeq::common_buffer_seqs(flushed->buffers, self->buffers, 
                    flushed.flushed_ofs(k) as int, buffer_gc as int, k);
            }
        }

    }

    proof fn compact_wf(self, start: nat, end: nat, compacted_buffer: SimpleBuffer)
        requires self.can_compact(start, end, compacted_buffer)
        ensures self.compact(start, end, compacted_buffer).wf()
    {
        let result = self.compact(start, end, compacted_buffer);
        assert forall |i| #[trigger] result.valid_child_index(i) implies self.valid_child_index(i) by {}
    }

    proof fn compact_buffer_property(self, start: nat, end: nat, compacted_buffer: SimpleBuffer)
        requires self.can_compact(start, end, compacted_buffer)
        ensures ({
            let slice_ofs_map = self.make_offset_map().decrement(start);
            let compact_slice = self->buffers.slice(start as int, end as int);
            &&& compacted_buffer == compact_slice.i_filtered(slice_ofs_map)
        }) 
    {
        let slice_ofs_map = self.make_offset_map().decrement(start);
        let compact_slice = self->buffers.slice(start as int, end as int);
        let compact_slice_i = compact_slice.i_filtered(slice_ofs_map);

        assert(compacted_buffer.map.dom() =~= compact_slice_i.map.dom()) by {
            compact_slice.i_filtered_from_domain(slice_ofs_map, 0);
            reveal(BetreeNode::valid_compact_key_domain);
        }

        
        assert forall |k| compacted_buffer.map.contains_key(k)
        implies #[trigger] compacted_buffer.map[k] == compact_slice_i.map[k] 
        by {
            reveal(BetreeNode::valid_compact_key_domain);
            let from = if self.flushed_ofs(k) <= start { 0 } else { self.flushed_ofs(k)-start };
            assert(slice_ofs_map.offsets[k] == from);
            assert(compacted_buffer.query(k) == compact_slice.query_from(k, from as int));
            assert(compacted_buffer.query(k) == compacted_buffer.map[k]);
            compact_slice.query_from_same_as_i_filtered(k, 0, slice_ofs_map);            
        }
        assert(compacted_buffer =~= compact_slice_i);
    }


    proof fn compact_commutes_with_i(self, start: nat, end: nat, compacted_buffer: SimpleBuffer)
        requires self.can_compact(start, end, compacted_buffer)
        ensures self.compact(start, end, compacted_buffer).i() == self.i()
    {
        let result = self.compact(start, end, compacted_buffer);
        self.compact_wf(start, end, compacted_buffer);

        broadcast use BetreeNode::i_wf;
        self.i_preserves_children(result, 0, self->children.len() as int);
        assert(result.i()->children =~= self.i()->children); // trigger

        result.i_buffer_domain();
        self.i_buffer_domain();

        let slice_ofs_map = self.make_offset_map().decrement(start);
        let result_ofs_map = result.make_offset_map();
        let compact_slice = self->buffers.slice(start as int, end as int);

        self.compact_buffer_property(start, end, compacted_buffer);
        
        assert forall |k| self.is_active_key(k) <==> result.is_active_key(k)
        by {
            if self.is_active_key(k) {
                let idx = self.instantiate_buffer_idx_for_active_key(k);
                if idx < start {
                    result.key_in_buffer_implies_active_key(k, idx);
                } else if idx < end {
                    assert(result->buffers[start as int] == compacted_buffer); // trigger
                    assert(compacted_buffer.map.contains_key(k)) by {
                        assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, idx-start)); // trigger
                        reveal(BetreeNode::valid_compact_key_domain);
                    }
                    result.key_in_buffer_implies_active_key(k, start as int);
                } else {
                    result.key_in_buffer_implies_active_key(k, idx - (end - start - 1));
                }
            }

            if result.is_active_key(k) {
                assert(result.i_buffer().map.contains_key(k)); // trigger
                let idx = result.instantiate_buffer_idx_for_active_key(k);
                if idx < start {
                    self.key_in_buffer_implies_active_key(k, idx);
                } else if idx < start+1 {
                    reveal(BetreeNode::valid_compact_key_domain);
                    let slice_idx = choose |slice_idx| compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, slice_idx);
                    self.key_in_buffer_implies_active_key(k, start + slice_idx);
                } else {
                    self.key_in_buffer_implies_active_key(k, idx + (end - start - 1));
                }
            }
        }


        assert forall |k| #[trigger] result.i()->buffer.map.contains_key(k)
        implies result.i()->buffer.map[k] == self.i()->buffer.map[k]
        by {
            self.query_from_refines(k);
            result.query_from_refines(k);

            let ofs = self.flushed_ofs(k) as int;
            let compacted_bufferseq = BufferSeq{buffers: seq![compacted_buffer]};
            assert(compacted_bufferseq.query_from(k, 1) == Message::Update{delta: nop_delta()}); // trigger
            assert(compacted_buffer.query(k) == compacted_bufferseq.query_from(k, 0)); // trigger

            if ofs < end {
                let slice_ofs = slice_ofs_map.offsets[k] as int;
                if !compacted_buffer.map.contains_key(k) {
                    assert forall |i| slice_ofs <= i < compact_slice.len()
                    implies ! #[trigger] compact_slice[i].map.contains_key(k)
                    by {
                        if compact_slice[i].map.contains_key(k) {
                            reveal(BetreeNode::valid_compact_key_domain);
                            assert(compact_slice.key_in_buffer_filtered(slice_ofs_map, 0, k, i)); // trigger
                        }
                    }
                    compact_slice.not_present_query_lemma(k, slice_ofs);
                }

                if ofs < start {
                    let left = self->buffers.slice(0, start as int);
                    BufferSeq::extend_buffer_seq_query_ensures(compact_slice, left, k, ofs);
                    BufferSeq::extend_buffer_seq_query_ensures(compacted_bufferseq, left, k, ofs);

                    assert(left.extend(compact_slice) =~= self->buffers.slice(0, end as int)); // trigger
                    assert(left.extend(compacted_bufferseq) =~= result->buffers.slice(0, start as int + 1)); // trigger
                
                    let right = self->buffers.slice(end as int, self->buffers.len() as int);
                    BufferSeq::extend_buffer_seq_query_ensures(right, self->buffers.slice(0, end as int), k, ofs);
                    BufferSeq::extend_buffer_seq_query_ensures(right, result->buffers.slice(0, start as int + 1), k, ofs);

                    assert(self->buffers.slice(0, end as int).extend(right) =~= self->buffers); // trigger
                } else  {
                    let right = self->buffers.slice(end as int, self->buffers.len() as int);
                    BufferSeq::extend_buffer_seq_query_ensures(right, compacted_bufferseq, k, 0);
                    BufferSeq::extend_buffer_seq_query_ensures(right, compact_slice, k, slice_ofs);
                    BufferSeq::common_buffer_seqs(compact_slice.extend(right), self->buffers, slice_ofs, start as int, k);
                    BufferSeq::common_buffer_seqs(compacted_bufferseq.extend(right), result->buffers, 0, start as int, k);
                }
            } else {
                BufferSeq::common_buffer_seqs(self->buffers, result->buffers, ofs, start+1-end, k);
            }   
        }
    }
} // end impl BetreeNode

pub open spec(checked) fn i_stamped_betree(stamped: StampedBetree) -> PivotBetree_v::StampedBetree
recommends
    stamped.value.wf(),
{
    Stamped{value: stamped.value.i(), seq_end: stamped.seq_end}
}

impl QueryReceiptLine{
    pub open spec(checked) fn i(self) -> PivotBetree_v::QueryReceiptLine
        recommends self.wf()
    {
        PivotBetree_v::QueryReceiptLine{node: self.node.i(), result: self.result}
    }
}

impl QueryReceipt{
    pub open spec(checked) fn i(self) -> PivotBetree_v::QueryReceipt
        recommends self.valid()
    {
        PivotBetree_v::QueryReceipt{
            key: self.key,
            root: self.lines[0].node.i(),
            lines: Seq::new(self.lines.len(), |i:int| self.lines[i].i())
        }
    }

    proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
    {
        broadcast use BetreeNode::i_wf;
        
        let i_receipt = self.i();
        assert forall |i| 0 <= i < i_receipt.lines.len()-1
        implies {
            &&& #[trigger] i_receipt.lines[i].node.key_in_domain(self.key)
            &&& i_receipt.child_linked_at(i) 
        } by {
            let node = self.lines[i].node;
            assert(node.key_in_domain(self.key)); // trigger

            node.i_children_lemma();
            assert(self.child_linked_at(i)); // trigger
            assert(node.valid_child_index(node->pivots.route(self.key) as nat)); // trigger
        }

        assert forall |i:int| 0 <= i < i_receipt.lines.len()-1
        implies #[trigger] i_receipt.result_linked_at(i) by {
            assert(self.result_linked_at(i)); // trigger
            self.lines[i].node.query_from_refines(self.key);
        }

        assert(i_receipt.all_lines_wf()); // trigger
    }
}

impl Path{
    pub open spec(checked) fn i(self) -> PivotBetree_v::Path
    recommends
        self.valid(),
    {
        PivotBetree_v::Path{node: self.node.i(), key: self.key, depth: self.depth}
    }

    proof fn subpath_commutes_with_i(self)
        requires self.valid(), 0 < self.depth
        ensures self.subpath().i() == self.i().subpath()
    {
        self.node.i_wf();
        self.node.i_children_lemma();
        assert(self.node.valid_child_index(self.node->pivots.route(self.key) as nat)); // trigger
    }

    proof fn i_valid(self)
        requires self.valid()
        ensures self.i().valid()
        decreases self.depth
    {
        self.node.i_wf();
        self.node.i_children_lemma();

        if 0 < self.depth {
            self.subpath_commutes_with_i();
            self.subpath().i_valid();

            assert forall |i| #[trigger] self.i().node.valid_child_index(i) 
            implies self.i().node->children[i as int] is Node by {
                assert(self.node.valid_child_index(i)); // trigger
             }
        }
    }

    proof fn target_wf(self)
        requires self.valid()
        ensures self.target().wf(), self.target() is Node
        decreases self.depth
    {
        if self.depth > 0 {
            self.subpath().target_wf();
        }
    }
    
    proof fn target_commutes_with_i(self)
        requires self.valid()
        ensures self.i().valid(), self.i().target() == self.target().i()
        decreases self.depth
    {
        self.i_valid();
        if 0 < self.depth {
            self.subpath().target_commutes_with_i();
            self.subpath_commutes_with_i();
        }
    }

    proof fn substitute_preserves_wf(self, replacement: BetreeNode)
        requires self.can_substitute(replacement)
        ensures self.substitute(replacement).wf()
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            self.subpath().substitute_preserves_wf(replacement);
    
            let result = self.substitute(replacement);
            if result is Node {
                self.replaced_children_matching_domains(replacement);
                assert(self.node.wf_children()); // trigger
                assert forall |i| #[trigger] result.valid_child_index(i) implies self.node.valid_child_index(i) by {}
            }
        }
    }

    proof fn replaced_children_matching_domains(self, replacement: BetreeNode)
        requires self.can_substitute(replacement), 0 < self.depth
        ensures self.node.children_have_matching_domains(self.replaced_children(replacement))
        decreases self.depth, 0nat
    {
                self.subpath().substitute_preserves_wf(replacement);

        let old_children = self.node->children;
        let new_children = self.replaced_children(replacement);
        
        if 0 < self.subpath().depth {
            self.subpath().replaced_children_matching_domains(replacement);
        }
    }

    proof fn substitute_commutes_with_i(self, replacement: BetreeNode)
        requires self.can_substitute(replacement)
        ensures self.substitute(replacement).wf(), 
            self.i().valid(), replacement.i().wf(),
            self.substitute(replacement).i() == self.i().substitute(replacement.i())
        decreases self.depth
    {
        self.i_valid();
        self.target_wf();
        self.substitute_preserves_wf(replacement);
        replacement.i_wf();

        
        if 0 < self.depth {
            let replaced = self.substitute(replacement);
            assert(replaced.make_offset_map() =~= self.node.make_offset_map()); // trigger

            self.target_commutes_with_i();
            self.subpath_commutes_with_i();
            self.i().substitute_preserves_wf(replacement.i());
            self.subpath().substitute_commutes_with_i(replacement);

            self.node.i_children_lemma();
            replaced.i_children_lemma();

            assert forall |i| 0 <= i < replaced->children.len()
            implies #[trigger] replaced.i()->children[i] =~= self.i().substitute(replacement.i())->children[i]
            by {
                assert(replaced.valid_child_index(i as nat)); // trigger
                assert(self.node.valid_child_index(i as nat)); // trigger
            }
            assert(replaced.i()->children =~= self.i().substitute(replacement.i())->children); // trigger
        }
    }

    proof fn substitute_noop(self, replacement: BetreeNode)
        requires self.valid(), replacement.wf(), 
            self.target().i() == replacement.i()
        ensures 
            self.substitute(replacement).wf(),
            self.substitute(replacement).i() == self.node.i()
        decreases self.depth
    {
        self.target_wf();
        self.substitute_preserves_wf(replacement);

        
        if 0 < self.depth {
            self.subpath().substitute_noop(replacement);
            assert(self.substitute(replacement).make_offset_map() =~= self.node.make_offset_map()); // trigger

            self.node.i_children_lemma();
            self.substitute(replacement).i_children_lemma();

            assert forall |i| 0 <= i < self.substitute(replacement)->children.len()
            implies #[trigger] self.substitute(replacement).i()->children[i] =~= self.node.i()->children[i]
            by {
                assert(self.substitute(replacement).valid_child_index(i as nat)); // trigger
                assert(self.node.valid_child_index(i as nat)); // trigger
            }
            assert(self.substitute(replacement).i()->children =~= self.node.i()->children); // trigger
        }
    }
}

impl FilteredBetree::Label {
    pub open spec(checked) fn i(self) -> PivotBetree::Label
    {
        match self {
            FilteredBetree::Label::Query{end_lsn, key, value} => PivotBetree::Label::Query{end_lsn: end_lsn, key: key, value: value},
            FilteredBetree::Label::Put{puts} => PivotBetree::Label::Put{puts: puts},
            FilteredBetree::Label::FreezeAs{stamped_betree} =>
                PivotBetree::Label::FreezeAs{stamped_betree:
                    if stamped_betree.value.wf() { i_stamped_betree(stamped_betree) }
                    else { arbitrary() } },
            FilteredBetree::Label::Internal{} => PivotBetree::Label::Internal{},
        }
    }
} // end impl FilteredBetree::Label

impl FilteredBetree::State {
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& (self.root is Node ==> self.root.my_domain() == total_domain())
    }

    pub open spec(checked) fn i(self) -> PivotBetree::State
    recommends
        self.wf(),
    {
        PivotBetree::State{root: self.root.i(), memtable: self.memtable}
    }

    pub proof fn i_inv(self)
        requires self.inv()
        ensures self.i().inv()
    {
        self.root.i_wf();
    }

    pub proof fn init_refines(self, stamped_betree: StampedBetree)
        requires FilteredBetree::State::initialize(self, stamped_betree)
        ensures PivotBetree::State::initialize(self.i(), i_stamped_betree(stamped_betree))
    {
        stamped_betree.value.i_wf();
    }

    proof fn query_refines(self, post: Self, lbl: FilteredBetree::Label, receipt: QueryReceipt)
        requires self.inv(), FilteredBetree::State::query(self, post, lbl, receipt)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::query(receipt.i()))
    {
        receipt.i_valid();
        reveal(PivotBetree::State::next_by);
    }

    proof fn put_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::put(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::put())
    {
        reveal(PivotBetree::State::next_by);
    }

    proof fn freeze_as_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::freeze_as(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::freeze_as())
    {
        self.root.i_wf();
        reveal(PivotBetree::State::next_by);
    }

    proof fn internal_flush_memtable_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_flush_memtable(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_flush_memtable())
    {
        self.root.i_wf();
        self.root.promote_commutes_with_i(total_domain());

        let promote = self.root.promote(total_domain());
        let buffers = BufferSeq{buffers: seq![self.memtable.buffer]};

        promote.extend_buffer_seq_wf(buffers);
        promote.extend_buffer_seq_refines_merge_buffer(buffers);

        let a = self.root.push_memtable(self.memtable).i();
        let b = self.root.i().push_memtable(self.memtable);
        
        assert forall |i| 0 <= i < a->children.len()
        implies a->children[i] == b->children[i]
        by {
            self.root.push_memtable(self.memtable).i_children_lemma();    
            if self.root is Node {
                self.root.i_children_lemma();
            }
        }

        assert(buffers.i().apply_filter(total_domain().key_set()) =~= buffers.i()); // trigger
        assert(buffers.i_from(1) == SimpleBuffer::empty()); // trigger
        assert(buffers.i() =~= buffers[0]); // trigger

        reveal(PivotBetree::State::next_by);
    }

    proof fn internal_grow_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_grow(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_grow())
    {
        broadcast use BetreeNode::i_wf;

        assert(post.i().root->children =~= self.i().root.grow()->children); // needs this for trigger?

        reveal(PivotBetree::State::next_by);
    }

    proof fn internal_split_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, request: SplitRequest)
        requires self.inv(), FilteredBetree::State::internal_split(self, post, lbl, path, request)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_split(path.i(), request))
    {
        broadcast use BetreeNode::i_wf;
        path.target().split_parent_wf(request);
        path.substitute_commutes_with_i(path.target().split_parent(request));

        path.i_valid();
        path.target_commutes_with_i();
        path.target().split_parent_commutes_with_i(request);

        reveal(PivotBetree::State::next_by);
    }

    proof fn internal_flush_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, child_idx: nat, buffer_gc: nat)
        requires self.inv(), FilteredBetree::State::internal_flush(self, post, lbl, path, child_idx, buffer_gc)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_flush(path.i(), child_idx))
    {
        broadcast use BetreeNode::i_wf;
        path.target().flush_wf(child_idx, buffer_gc);
        path.substitute_commutes_with_i(path.target().flush(child_idx, buffer_gc));

        path.i_valid();
        path.target_commutes_with_i();
        path.target().flush_commutes_with_i(child_idx, buffer_gc);

        reveal(PivotBetree::State::next_by);
    }

    proof fn internal_compact_refines(self, post: Self, lbl: FilteredBetree::Label, path: Path, start: nat, end: nat, compacted_buffer: SimpleBuffer)
        requires self.inv(), FilteredBetree::State::internal_compact(self, post, lbl, path, start, end, compacted_buffer)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_noop())
    {
        broadcast use BetreeNode::i_wf;
        path.target().compact_wf(start, end, compacted_buffer);
        path.target().compact_commutes_with_i(start, end, compacted_buffer);
        path.substitute_noop(path.target().compact(start, end, compacted_buffer));        

        reveal(PivotBetree::State::next_by);
    }

    proof fn internal_noop_noop(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::internal_noop(self, post, lbl)
        ensures post.inv(), PivotBetree::State::next_by(self.i(), post.i(), lbl.i(), PivotBetree::Step::internal_noop())
    {
        broadcast use BetreeNode::i_wf;
        reveal(PivotBetree::State::next_by);
    }

    pub proof fn next_refines(self, post: Self, lbl: FilteredBetree::Label)
        requires self.inv(), FilteredBetree::State::next(self, post, lbl),
        ensures post.inv(), PivotBetree::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(FilteredBetree::State::next);
        reveal(FilteredBetree::State::next_by);
        reveal(PivotBetree::State::next);

        match choose |step| FilteredBetree::State::next_by(self, post, lbl, step)
        {
            FilteredBetree::Step::query(receipt) => { self.query_refines(post, lbl, receipt); } 
            FilteredBetree::Step::put() => { self.put_refines(post, lbl); }
            FilteredBetree::Step::freeze_as() => { self.freeze_as_refines(post, lbl); }
            FilteredBetree::Step::internal_flush_memtable() => { self.internal_flush_memtable_refines(post, lbl); }
            FilteredBetree::Step::internal_grow() => { self.internal_grow_refines(post, lbl); }
            FilteredBetree::Step::internal_split(path, split_request) => { self.internal_split_refines(post, lbl, path, split_request); }
            FilteredBetree::Step::internal_flush(path, child_idx, buffer_gc) => { self.internal_flush_refines(post, lbl, path, child_idx, buffer_gc); }
            FilteredBetree::Step::internal_compact(path, start, end, compacted_buffer) => { self.internal_compact_refines(post, lbl, path, start, end, compacted_buffer); }
            FilteredBetree::Step::internal_noop() => { self.internal_noop_noop(post, lbl); }
            _ => { assert(false); } 
        }
    }
} // end impl FilteredBetree::State

}//verus
