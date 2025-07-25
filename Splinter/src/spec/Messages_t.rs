// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

verus! {

#[derive(Clone,Copy,Debug)]
pub struct Value(pub u64);

#[derive(Clone,Copy,Debug)]
pub struct Delta(pub u64);

// TODO(jonh): Need to genericize the types of Key, Value; and then we'll need to axiomitify /
// leave-unspecified a default value
pub open spec(checked) fn default_value() -> Value {
    Value(0)
}

// TODO: placeholder
pub open spec(checked) fn nop_delta() -> Delta {
    Delta(0)
}

/// Messages represent operations that can be performed to update/define the
/// state of values in a map.
/// Messages can themselves be used as the values of a map as long as only "Define"
/// messages are stored (see TotalKMMap).
#[derive(Clone,Copy,Debug)]
pub enum Message {
    /// A Define message represents setting a variable to the given value.
    Define { value: Value },
    /// An Update message represents updating a variable by the given delta.
    Update { delta: Delta },
}

impl Message {
    // place holder since we don't use deltas yet
    pub open spec(checked) fn combine_deltas(new: Delta, old: Delta) -> Delta {
        if new == nop_delta() {
            old
        } else if old == nop_delta() {
            new
        } else {
            // nop_delta()
            new
        }
    }

    // Place holder. Eventually applying a delta should apply some offset.
    pub open spec(checked) fn apply_delta(delta: Delta, value: Value) -> Value {
        value
    }

    pub open spec(checked) fn merge(self, new: Message) -> Message {
        match (self, new) {
            (_, Message::Define { value: new_value }) => { Message::Define { value: new_value } },
            (Message::Update { delta: old_delta }, Message::Update { delta: new_delta }) => {
                Message::Update { delta: Self::combine_deltas(new_delta, old_delta) }
            },
            (Message::Define { value }, Message::Update { delta }) => {
                Message::Define { value: Self::apply_delta(delta, value) }
            },
        }
    }

    pub open spec(checked) fn empty() -> Message {
        Message::Define { value: default_value() }  // TODO: This is a placeholder

    }// pub proof fn merge_associativity(a: Message, b: Message, c: Message)
    //     ensures a.merge(b.merge(c)) == a.merge(b).merge(c)
    // {
    // }

}

} // verus!
