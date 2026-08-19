// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Crash-aware ownership of the persistent and in-flight superblock page.

use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::RawPage;

verus! {

state_machine!{ SuperblockStore {
    fields {
        pub persistent: RawPage,
        pub in_flight: Option<RawPage>,
        pub landed: bool,
    }

    pub enum Label {
        Write{ raw: RawPage },
        Land,
        Complete,
        Crash,
    }

    init!{ initialize(raw: RawPage) {
        init persistent = raw;
        init in_flight = Option::None;
        init landed = false;
    }}

    transition!{ write(lbl: Label) {
        require let Label::Write{raw} = lbl;
        require pre.in_flight is None;
        require !pre.landed;
        update in_flight = Option::Some(raw);
    }}

    transition!{ land(lbl: Label) {
        require lbl is Land;
        require pre.in_flight is Some;
        update persistent = pre.in_flight.unwrap();
        update in_flight = Option::None;
        update landed = true;
    }}

    transition!{ complete(lbl: Label) {
        require lbl is Complete;
        require pre.in_flight is None;
        require pre.landed;
        update landed = false;
    }}

    transition!{ crash(lbl: Label) {
        require lbl is Crash;
        update in_flight = Option::None;
        update landed = false;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        self.in_flight is Some ==> !self.landed
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, raw: RawPage) {}

    #[inductive(write)]
    fn write_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(land)]
    fn land_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(complete)]
    fn complete_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {}
}}

impl SuperblockStore::State {
    pub proof fn inv_next(
        pre: Self,
        post: Self,
        lbl: SuperblockStore::Label,
    )
        requires
            pre.inv(),
            SuperblockStore::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        let step = choose |step|
            SuperblockStore::State::next_by(pre, post, lbl, step);
        match step {
            SuperblockStore::Step::write() => {
            },
            SuperblockStore::Step::land() => {
            },
            SuperblockStore::Step::complete() => {
            },
            SuperblockStore::Step::crash() => {
            },
            SuperblockStore::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        };
    }
}

} // verus!
