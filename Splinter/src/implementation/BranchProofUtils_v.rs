// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Proof utilities shared by the active bulk-branch implementation. These do
// not depend on the legacy mutable AllocationBranch state machine.

use vstd::prelude::*;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::disk::GenericDisk_v::{AU, Address};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

pub open spec fn tight_branch_in_loose_disk(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
    branch: LinkedBranch<Summary>,
) -> bool
{
    &&& branch.root == root
    &&& branch.valid_sealed_branch()
    &&& branch.tight_disk_view_with_summary()
    &&& branch.get_summary() == summary
    &&& branch.disk_view.entries <= loose_disk.entries
}

pub proof fn mini_allocator_add_aus_preserves_all_aus(
    mini_allocator: MiniAllocator,
    aus: Set<AU>,
)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.add_aus(aus).all_aus() == mini_allocator.all_aus() + aus,
{
    assert forall |au: AU| #[trigger] mini_allocator.add_aus(aus).all_aus().contains(au)
        <==> (mini_allocator.all_aus() + aus).contains(au) by { };
}

pub proof fn mini_allocator_allocate_preserves_all_aus(
    mini_allocator: MiniAllocator,
    addr: Address,
)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(addr),
    ensures
        mini_allocator.allocate(addr).all_aus() == mini_allocator.all_aus(),
{
    assert forall |au: AU| #[trigger] mini_allocator.allocate(addr).all_aus().contains(au)
        <==> mini_allocator.all_aus().contains(au) by {
        if au == addr.au {
            assert(mini_allocator.all_aus().contains(au));
        }
    };
}

pub open spec fn append_put_message(msg: Message) -> Message
{
    msg
}

pub open spec fn append_puts_up_to(
    start_lsn: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    end: nat,
) -> MsgHistory
    recommends
        end <= keys.len(),
        keys.len() == msgs.len(),
{
    let seq_end = start_lsn + end;
    let puts = Map::new(
        |lsn: nat| start_lsn <= lsn < seq_end,
        |lsn: nat| {
            let idx = (lsn - start_lsn) as int;
            KeyedMessage { key: keys[idx], message: append_put_message(msgs[idx]) }
        },
    );
    MsgHistory { msgs: puts, seq_start: start_lsn, seq_end }
}

pub open spec fn append_puts(
    start_lsn: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
) -> MsgHistory
    recommends
        keys.len() == msgs.len(),
{
    append_puts_up_to(start_lsn, keys, msgs, keys.len() as nat)
}

pub proof fn append_puts_wf(start_lsn: nat, keys: Seq<Key>, msgs: Seq<Message>)
    requires
        keys.len() == msgs.len(),
    ensures
        append_puts(start_lsn, keys, msgs).wf(),
        append_puts(start_lsn, keys, msgs).seq_start == start_lsn,
        append_puts(start_lsn, keys, msgs).seq_end == start_lsn + keys.len(),
{
    let puts = append_puts(start_lsn, keys, msgs);
    assert(puts.seq_start <= puts.seq_end);
    assert forall |lsn: nat| #[trigger] puts.msgs.dom().contains(lsn)
        <==> puts.contains(lsn) by { };
}

} // verus!
