// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[allow(unused_imports)]
use vstd::prelude::*;

//use vstd::prelude_macros::*;
use verus_state_machines_macros::state_machine;
#[allow(unused_imports)]
use vstd::{map::*};

// use crate::spec::Option_t::*;
use crate::abstract_system::StampedMap_v::{LSN, empty};
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;

verus! {

pub type StoreImage = MsgHistory;

// TODO: Could use option types? But they are not supported in verus
pub enum Ephemeral {
    Unknown,
    Known{ v: AbstractJournal::State },
}

impl Ephemeral
{
    pub open spec(checked) fn wf(self) -> bool
    {
      self is Known ==> self->v.wf()
    }
}

// AbstractCrashAwareJournal represents an infinite MsgHistory with a persisted
// version as well as an ephemeral (in-memory) version. The Journal is
// able to crash and recover. A crash-aware version of AbstractJournal.
state_machine!{ AbstractCrashAwareJournal {
    fields {
        /// The persisted snapshot of the journal (stores a MsgHistory directly).
        pub persistent: StoreImage,
        /// The in-memory view of the journal. If Known, it just wraps an
        /// AbstractJournal::State (which just contains a MsgHistory). 
        pub ephemeral: Ephemeral,
        /// A valid snapshot of the journal that may be committed by a later
        /// coordination-level superblock write.
        pub frozen: Option<StoreImage>
    }

    init!{
        initialize() {  // mkfs -- notice empty persistent
            init persistent = MsgHistory{ msgs: Map::empty(), seq_start: 0, seq_end: 0};
            init ephemeral = Ephemeral::Unknown;
            init frozen = Option::None;
        }
    }

    pub enum Label {
        LoadEphemeralFromPersistentLabel,
        ReadForRecoveryLabel{ records: MsgHistory },
        QueryEndLsnLabel{ end_lsn: LSN },
        PutLabel{ records: MsgHistory },
        InternalLabel,
        QueryLsnPersistenceLabel{ sync_lsn: LSN },
        CommitStartLabel{ new_boundary_lsn: LSN, frozen_journal: StoreImage },
        // TODO(remove require_end)???
        CommitCompleteLabel{ require_end: LSN },

        // NB a modeling design choice:
        // At this level, we're modeling the disk contents in the `persistent` view of the map &
        // journal, which are *also* models of what the program thinks is on the disk. To so
        // overload that field, there's a place where they diverge: in a crash. In a crash,
        // the actual program "forgets" everything, which means the persistent view is a model
        // of what the program will see once it starts reading the disk after reinitializing.
        // What it sees depends on whether an in-flight superblock landed.
        //
        // An alternative design would separately model the disk state, and have a separate step
        // representing the disk applying an in-flight superblock change. But that approach would
        // introduce other fictions: presumably we don't want to model asynchrony of all the other
        // disk writes at this level of abstraction.
        CrashLabel{ keep_in_flight: bool },
    }

    transition!{
        // Copy the persistent state into the ephemeral state
        // Should only transition from a state where the ephemeral
        // state is unknown.
        // (Transition name is pretty comprehensive on this one)
        load_ephemeral_from_persistent(lbl: Label, new_journal: AbstractJournal::State) {
            require lbl is LoadEphemeralFromPersistentLabel;
            require pre.ephemeral is Unknown;
            require AbstractJournal::State::init_by(new_journal, AbstractJournal::Config::initialize(pre.persistent));
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        // Read a section of the journal. Transition asserts that the
        // records in the label correspond to a real and valid slice
        // of the journal (rather than made up or random values).
        read_for_recovery(lbl: Label) {
            require lbl is ReadForRecoveryLabel;
            require pre.ephemeral is Known;

            require AbstractJournal::State::next(
                pre.ephemeral->v, 
                pre.ephemeral->v, 
                AbstractJournal::Label::ReadForRecoveryLabel{ messages: lbl.arrow_ReadForRecoveryLabel_records() }
            );
        }
    }

    transition!{
        query_end_lsn(lbl: Label) {
            require lbl is QueryEndLsnLabel;
            require pre.ephemeral is Known;
            require AbstractJournal::State::next(
                pre.ephemeral->v, 
                pre.ephemeral->v, 
                AbstractJournal::Label::QueryEndLsnLabel{ end_lsn: lbl->end_lsn },
            );
        }
    }

    transition!{
        put(lbl: Label, new_journal: AbstractJournal::State) {
            require lbl is PutLabel;
            require pre.ephemeral is Known;
            require AbstractJournal::State::next(
                pre.ephemeral->v, 
                new_journal, 
                AbstractJournal::Label::PutLabel{ messages: lbl.arrow_PutLabel_records() },
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        internal(lbl: Label, new_journal: AbstractJournal::State) {
            require lbl is InternalLabel;
            require pre.ephemeral is Known;
            require AbstractJournal::State::next(
                pre.ephemeral->v, 
                new_journal,
                AbstractJournal::Label::InternalLabel,
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        query_lsn_persistence(lbl: Label) {
            require lbl is QueryLsnPersistenceLabel;
            require lbl->sync_lsn <= pre.persistent.seq_end;
        }
    }

    transition!{
        commit_start(lbl: Label) {
            require lbl is CommitStartLabel;
            require pre.ephemeral is Known;
            require pre.frozen is None;

            let frozen_journal = lbl->frozen_journal;
            require frozen_journal.wf();

            // Frozen journal stitches to frozen map
            require frozen_journal.seq_start == lbl->new_boundary_lsn;

            // The durable journal endpoint does not go backwards. Journal-only
            // sync may advance it while retaining the map boundary.
            require pre.persistent.seq_end <= frozen_journal.seq_end;
            require AbstractJournal::State::next(
                pre.ephemeral->v,
                pre.ephemeral->v,
                AbstractJournal::Label::FreezeForCommitLabel{ frozen_journal },
            );
            update frozen = Option::Some(frozen_journal);
        }
    }

    transition!{
        commit_complete(lbl: Label, new_journal: AbstractJournal::State) {
            require lbl is CommitCompleteLabel;
            require pre.ephemeral is Known;
            require pre.frozen is Some;

            require AbstractJournal::State::next(
                pre.ephemeral->v, 
                new_journal, 
                AbstractJournal::Label::DiscardOldLabel{ 
                    start_lsn: pre.frozen.unwrap().seq_start,
                    require_end: lbl->require_end
                },
            );
            
            // Watch the `update` keyword!
            update persistent = pre.frozen.unwrap();
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update frozen = Option::None;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl is CrashLabel;
            require lbl->keep_in_flight ==> pre.frozen is Some;
            update ephemeral = Ephemeral::Unknown;
            update frozen = Option::None;
            update persistent = if lbl->keep_in_flight { pre.frozen.unwrap() } else { pre.persistent };
        }
    }
}}
}
