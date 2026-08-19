// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::betree::Buffer_v::{Buffer, SimpleBuffer};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::{DiskView, LinkedBranch, Node};
use crate::allocation_layer::Likes_v::restrict_domain_au;
use crate::disk::GenericDisk_v::{addrs_closed, AU, Address};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

pub type Summary = Set<AU>;
pub type BranchNode = Node<Summary>;

impl BufferDisk<BranchNode> {
    pub open spec fn to_branch_disk(self) -> DiskView<Summary> {
        DiskView { entries: self.entries }
    }

    pub open spec fn get_branch(self, root: Address) -> LinkedBranch<Summary> {
        LinkedBranch {
            root,
            disk_view: self.to_branch_disk(),
        }
    }
}

impl Buffer for BranchNode {
    open spec fn linked_contains(
        self,
        dv: BufferDisk<Self>,
        addr: Address,
        key: Key,
    ) -> bool {
        let branch = dv.get_branch(addr);
        if branch.acyclic() {
            branch.contains_internal(branch.the_ranking(), key)
        } else {
            false
        }
    }

    open spec fn linked_query(
        self,
        dv: BufferDisk<Self>,
        addr: Address,
        key: Key,
    ) -> Message {
        LinkedBranch {
            root: addr,
            disk_view: DiskView { entries: dv.entries },
        }.query(key)
    }

    open spec fn i(
        self,
        dv: BufferDisk<Self>,
        addr: Address,
    ) -> SimpleBuffer {
        LinkedBranch {
            root: addr,
            disk_view: DiskView { entries: dv.entries },
        }.i().i()
    }
}

impl LinkedBranch<Summary> {
    pub open spec fn get_summary(self) -> Summary
        recommends self.has_root()
    {
        if self.root() is Index {
            self.disk_view.get(self.root()->aux_ptr.unwrap())->0
        } else {
            set![self.root.au]
        }
    }

    pub open spec(checked) fn seal(self, addr: Address, summary: Summary) -> Self
        recommends self.has_root() && self.root() is Index
    {
        let new_aux_node = Node::Auxiliary(summary);
        let new_root_node = Node::Index {
            pivots: self.root()->pivots,
            children: self.root()->children,
            aux_ptr: Some(addr),
        };
        LinkedBranch {
            disk_view: self.disk_view.modify_disk(addr, new_aux_node)
                .modify_disk(self.root, new_root_node),
            ..self
        }
    }

    pub open spec fn sealed_root(self) -> bool
    {
        &&& self.has_root()
        &&& self.root() is Index ==> {
            &&& self.root()->aux_ptr is Some
            &&& self.disk_view.valid_address(self.root()->aux_ptr.unwrap())
            &&& self.disk_view.entries[self.root()->aux_ptr.unwrap()] is Auxiliary
        }
    }

    pub open spec fn full_repr(self) -> Set<Address>
    {
        if self.root() is Index {
            self.representation() + set![self.root()->aux_ptr.unwrap()]
        } else {
            self.representation()
        }
    }

    pub open spec fn tight_disk_view_with_summary(self) -> bool
    {
        self.disk_view.representation() == self.full_repr()
    }

    pub open spec fn valid_sealed_branch(self) -> bool
    {
        &&& self.inv()
        &&& self.sealed_root()
        &&& addrs_closed(self.full_repr(), self.get_summary())
        &&& restrict_domain_au(self.disk_view.entries, self.get_summary()) =~= self.full_repr()
    }
}

} // verus!
