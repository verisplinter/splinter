// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::StampedMap_v::Stamped;
use crate::allocation_layer::AllocationBranch_v::AllocationBranch;
use crate::betree::Buffer_v::SimpleBuffer;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{default_value, nop_delta, Message, Value};
use crate::spec::TotalKMMap_t::TotalKMMap;

verus! {

pub open spec fn normalize_value(msg: Message) -> Value
{
    match msg {
        Message::Define{value} => value,
        Message::Update{delta} => Message::apply_delta(delta, default_value()),
    }
}

pub open spec fn normalize_message(msg: Message) -> Message
{
    Message::Define{value: normalize_value(msg)}
}

pub struct AllocationBranchStack {
    pub branches: Seq<AllocationBranch>,
    pub seq_end: nat,
}

impl AllocationBranchStack {
    pub open spec fn is_nop_message(msg: Message) -> bool
    {
        msg == Message::Update{delta: nop_delta()}
    }

    pub open spec fn active_idx(self) -> int
        recommends self.branches.len() > 0
    {
        self.branches.len() - 1
    }

    pub open spec fn active_branch(self) -> AllocationBranch
        recommends self.branches.len() > 0
    {
        self.branches[self.active_idx()]
    }

    pub open spec fn branch_sparse_map(branch: AllocationBranch) -> Map<Key, Message>
    {
        if branch.branch is Some {
            let raw_map = branch.branch.unwrap().i().i().map;
            Map::new(
                |k: Key| raw_map.contains_key(k) && !Self::is_nop_message(raw_map[k]),
                |k: Key| raw_map[k],
            )
        } else {
            Map::empty()
        }
    }

    pub open spec fn branch_sparse_buffer(branch: AllocationBranch) -> SimpleBuffer
    {
        SimpleBuffer { map: Self::branch_sparse_map(branch) }
    }

    pub open spec fn sparse_map_up_to(branches: Seq<AllocationBranch>, end: nat) -> Map<Key, Message>
        recommends end <= branches.len()
        decreases end
    {
        if end == 0 {
            Map::empty()
        } else {
            Self::sparse_map_up_to(branches, (end - 1) as nat)
                .union_prefer_right(Self::branch_sparse_map(branches[(end - 1) as int]))
        }
    }

    pub open spec fn sparse_map(self) -> Map<Key, Message>
    {
        Self::sparse_map_up_to(self.branches, self.branches.len() as nat)
    }

    pub open spec fn sparse_buffer(self) -> SimpleBuffer
    {
        SimpleBuffer { map: self.sparse_map() }
    }

    pub open spec fn query_up_to(branches: Seq<AllocationBranch>, end: nat, key: Key) -> Message
        recommends end <= branches.len()
        decreases end
    {
        if end == 0 {
            Message::Update{delta: nop_delta()}
        } else {
            let msg = Self::branch_sparse_buffer(branches[(end - 1) as int]).query(key);
            if Self::is_nop_message(msg) {
                Self::query_up_to(branches, (end - 1) as nat, key)
            } else {
                msg
            }
        }
    }

    pub open spec fn query(self, key: Key) -> Message
    {
        Self::query_up_to(self.branches, self.branches.len() as nat, key)
    }

    pub open spec fn kmmap_i(self) -> TotalKMMap
    {
        TotalKMMap(Map::new(
            |k: Key| true,
            |k: Key| normalize_message(self.sparse_buffer().query(k)),
        ))
    }

    pub open spec fn abstract_map_i(self) -> AbstractMap::State
    {
        AbstractMap::State {
            stamped_map: Stamped {
                value: self.kmmap_i(),
                seq_end: self.seq_end,
            }
        }
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.branches.len() > 0
        &&& forall |i: int|
            0 <= i < self.branches.len() - 1
            ==> {
                &&& #[trigger] self.branches[i].inv()
                &&& self.branches[i].sealed
            }
        &&& self.active_branch().inv()
        &&& !self.active_branch().sealed
        &&& forall |i: int, j: int|
            0 <= i < j < self.branches.len()
            ==> self.branches[i].mini_allocator.all_aus().disjoint(self.branches[j].mini_allocator.all_aus())
        &&& self.abstract_map_i().stamped_map.value.wf()
    }
}

}
