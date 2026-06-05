// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
/// AbstractCrashAwareSystem. Formerly named AbstractCoordinationSystem.
/// Coordinates a map and a journal to present a unified map once abstracted.
///
/// This is the final refinement layer before the top level trusted spec.

use vstd::prelude::*;

//use vstd::prelude_macros::*;
use verus_state_machines_macros::state_machine;
use vstd::prelude::*;

use crate::spec::Messages_t::Message;
use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap, EphemeralState, ID, Input, Output, Reply, Request, SyncReqId};

use crate::abstract_system::AbstractCrashAwareJournal_v::*;
use crate::abstract_system::AbstractCrashAwareMap_v::*;
use crate::abstract_system::StampedMap_v::{LSN, StampedMap, empty};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};

// TODO (jonh): Rename all of the labels in all files to exclude "Op" or "Label" since it's redundant
// as enums are already namespaced under "Label", so it's like saying "Label Label"

verus! {

/// SyncReqId's are used to assign sync requests unique IDs. Actual value is meaningless beyond
/// identifying a specific sync request.
// type SyncReqId = nat;

/// SyncReqs represents a set of outstanding sync requests. Sync requests are stored as key-value
/// pairs: (key, lsn), where "key" is the sync request ID, and "lsn" was the last executed
/// LSN on the map at the time the sync request was made.
type SyncReqs = Map<SyncReqId, LSN>;

state_machine!{ CoordinationSystem {
  fields {
    /// The state of the journal in our system.
    pub journal: AbstractCrashAwareJournal::State,

    /// State of the map backing our system.
    pub mapadt: AbstractCrashAwareMap::State,

    /// Tracks the set of outstanding client requests and undelivered replies.
    pub progress: MapSpec_t::EphemeralState,

    /// The set of outstanding sync requests.
    pub sync_reqs: SyncReqs,

    /// The state of the async disk buffer: is there a superblock write in-flight,
    /// or has it landed on the disk? Used to refine when a spec Sync event occurs.

    // This entire state machine is an abstraction of the ultimate implementation system, which is
    // a trusted composition of a trusted disk and its async buffers with the untrusted program
    // (and its in-memory state). At this level, the disk state is abstracted into the journal and
    // the mapadt. Those models aren't "precise" with respect to the trusted disk at the bottom
    // layer, in that they're only updated asynchronously as the program learns that writes have
    // completed. But that doesn't really affect the refinement task.
    //
    // To precisely model the sync transition, however, we also need to know exactly when each
    // superblock write hits the disk, for that is the moment when the spec version list has old
    // versions discarded.
    //
    // In a previous version of this model, we didn't capture this state; instead, we just delayed
    // declaring the abstract "Sync" event until the program learned (in the commit_complete step)
    // that the commit had landed. The "sync" acted, in practice, as a "right mover" in the
    // abstract spec.
    //
    // That scheme produced a valid refinement, but not really the intuitive one.  Nothing about
    // that scheme was bogus: it wasn't unsound, nor did it represent a trusted spec that admitted
    // executions we really didn't want to admit. But it was difficult to explain; it required
    // apologizing for the fact that we were justifying the intuitive "real" execution with an
    // "equally acceptable but not really the right" other execution.
    pub superblock_in_flight: bool,

    /// The commit superblock write has landed, but the program has not yet
    /// completed the commit protocol and cleared the frozen component images.
    pub superblock_landed: bool,
  }

  // Labels of coordinationsystem should directly be the labels of the
  // CrashTolerantAsyncMap labels. Ideal would be to just copy it somehow,
  // but for now we're just wrapping the CTAM ones.
  pub enum Label{
    Label{ ctam_label: CrashTolerantAsyncMap::Label }
  }

  init! {
    // Raise the non-determinism to the caller level (functional style)
    // initialize(j: AbstractCrashAwareJournal::State, m: AbstractCrashAwareMap::State) {
    //   require AbstractCrashAwareJournal::State::initialize(j);
    //   require AbstractCrashAwareMap::State::initialize(m)
    //   init journal = j;
    //   init mapadt = m;
    //   init ephemeral = Ephemeral::Unknown;
    // }

    // "Predicate-style" (give me the state and I verify it's good for initial state)
    initialize(state: CoordinationSystem::State) {
      // "Looks good to me" - Jon
      // "Doesn't look so good to me anymore" - Tenzin (later on)
      // Issue is that this would just allow any arbitrary journal and
      // mapadt past, but we only want journals and mapadts that meet
      // a certain condition. How to do that?
      require AbstractCrashAwareJournal::State::init(state.journal);
      require AbstractCrashAwareMap::State::init(state.mapadt);
      init journal = state.journal;
      init mapadt = state.mapadt;
      init progress = AsyncMap::State::init_ephemeral_state();
      init sync_reqs = Map::empty();
      init superblock_in_flight = false;
      init superblock_landed = false;
    }
  }

	  transition! {
	    noop(
	      label: Label,
	    ) {
	      let ctam_label = label->ctam_label;
	      require ctam_label is Noop;
	    }
	  }

	  transition! {
	    // Load the state of the ephemeral journal and map from the persistent
	    // state (just a direct copy)
	    load_ephemeral_from_persistent(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
      new_mapadt: AbstractCrashAwareMap::State,
    ) {
      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::Noop } = label;
      
      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::LoadEphemeralFromPersistentLabel
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::LoadEphemeralFromPersistentLabel{ end_lsn: pre.mapadt.persistent.seq_end }
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    // Apply records from the journal to the ephemeral map when the ephemeral
    // map is still behind.
    recover(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
      new_mapadt: AbstractCrashAwareMap::State,
      records: MsgHistory,
    ) {
      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::Noop } = label;

      require records.wf();

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::ReadForRecoveryLabel{ records }
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::PutRecordsLabel{ records }
      );

      update journal = new_journal;
      update mapadt = new_mapadt; 
    }
  }

  transition! {
    // accept_request indicates when the coordination system receives
    // a request for an operation on the abstract key-value store. We don't
    // execute it yet, this transition just notes that the request has occurred
    // at this point.
    accept_request(
      label: Label,
    ) {
      // Tenzin: Each of these destructurings requires looking
      // up in another file what the fully qualified name of the type
      // is and that's annoying. Good intellisense would save us here
      require let Label::Label{
        ctam_label: CrashTolerantAsyncMap::Label::OperateOp{
          base_op: AsyncMap::Label::RequestOp{
            req
          }
        }
      } = label;

      let Label::Label{ ctam_label } = label;

      // Alternative syntax for destructuring and matching enum type
      // require ctam_label is OperateOp;
      // let base_op = ctam_label->base_op;
      // require base_op is RequestOp;
      // let req = base_op->req;

      require !pre.progress.requests.contains(req);

      update progress = MapSpec_t::EphemeralState{
        requests: pre.progress.requests.insert(req),
        ..pre.progress
      };
    }
  }

  transition! {
    // Execute a previously requested query on the kv-store.
    query(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
      new_mapadt: AbstractCrashAwareMap::State,
    ) {
      let current_lsn = pre.mapadt.i().seq_end;

      // The query transition label is labeled with the input and output of the
      // query operation. We want to dissect that information out so that we can
      // require that we only execute a query transition if it corresponds to a
      // previously requested query (as well as assert that enums are of right
      // type along the way). (Unfortunately this requires a series of rather
      // ugly calls).
      let ctam_label = label->ctam_label;

      require ctam_label is OperateOp;
      let base_op = ctam_label->base_op;
      require base_op is ExecuteOp;
      let req = base_op.arrow_ExecuteOp_req();
      let reply = base_op.arrow_ExecuteOp_reply();
      require req.input is QueryInput;
      require reply.output is QueryOutput;
      let key = req.input.arrow_QueryInput_key();
      let value = reply.output->value;

      require pre.progress.requests.contains(req);
      require req.id == reply.id;

      require !pre.progress.replies.contains(reply);

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::QueryEndLsnLabel{end_lsn: current_lsn},
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::QueryLabel{
          end_lsn: current_lsn,
          key: key,
          value: value,
        },
      );

      // Remove the request from outstanding requests, and add corresponding
      // response to set of undelivered replies.
      update progress = MapSpec_t::EphemeralState{
        requests: pre.progress.requests.remove(req),
        replies: pre.progress.replies.insert(reply),
      };
      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    put(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
      new_mapadt: AbstractCrashAwareMap::State,
    ) {
      let current_lsn = pre.mapadt.i().seq_end;

      // Destructuring and label checking boilerplate
      require let Label::Label{
        ctam_label: CrashTolerantAsyncMap::Label::OperateOp{
          base_op: AsyncMap::Label::ExecuteOp{
            req,
            reply,
          }
        }
      } = label;

      require let Request{
        input: Input::PutInput{
          key,
          value,
        },
        id: request_id,
      } = req;

      require let Reply{
        output: Output::PutOutput,
        id: reply_id,
      } = reply;

      require pre.progress.requests.contains(req);
      require req.id == reply.id;
      require !pre.progress.replies.contains(reply);

      // TODO: let keyed_message = 
      let keyed_message = KeyedMessage{
        key: key,
        message: Message::Define { value: value },
      };
      // TODO: let singleton: MsgHistory = <something>;
      let singleton = MsgHistory::singleton_at(current_lsn, keyed_message);

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::PutLabel{ records: singleton },
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::PutRecordsLabel{ records: singleton },
      );

      update progress = MapSpec_t::EphemeralState{
        requests: pre.progress.requests.remove(req),
        replies: pre.progress.replies.insert(reply),
      };
      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    execute_noop(label: Label) {
      let ctam_label = label->ctam_label;

      require ctam_label is OperateOp;
      let base_op = ctam_label->base_op;
      require base_op is ExecuteOp;
      let req = base_op.arrow_ExecuteOp_req();
      let reply = base_op.arrow_ExecuteOp_reply();
      require req.input is NoopInput;
      require reply.output is NoopOutput;

      require pre.progress.requests.contains(req);
      require req.id == reply.id;
      require !pre.progress.replies.contains(reply);

      update progress = MapSpec_t::EphemeralState{
        requests: pre.progress.requests.remove(req),
        replies: pre.progress.replies.insert(reply),
      };
    }
  }

  transition! {
    deliver_reply(label: Label) {
      let ctam_label = label->ctam_label;

      require ctam_label is OperateOp;
      
      let base_op = ctam_label->base_op;
      require base_op is ReplyOp;

      let reply = base_op.arrow_ReplyOp_reply();

      require pre.progress.replies.contains(reply);
      update progress = MapSpec_t::EphemeralState {
        replies: pre.progress.replies.remove(reply),
        ..pre.progress
      };
    }
  }

  transition! {
    journal_internal(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
    ) {
      let ctam_label = label->ctam_label;
      require ctam_label is Noop;

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::InternalLabel,
      );

      update journal = new_journal;
    }
  }

  transition! {
    map_internal(
      label: Label,
      new_mapadt: AbstractCrashAwareMap::State,
    ) {
      let ctam_label = label->ctam_label;
      require ctam_label is Noop;

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::InternalLabel,
      );

      update mapadt = new_mapadt;
    }
  }

  transition! {
    req_sync(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
    ) {
      let current_lsn = pre.mapadt.i().seq_end;

      let ctam_label = label->ctam_label;
      require ctam_label is ReqSyncOp;

      let sync_req_id = ctam_label.arrow_ReqSyncOp_sync_req_id();
      require !pre.sync_reqs.dom().contains(sync_req_id);
      
      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::QueryEndLsnLabel{ end_lsn: current_lsn },
      );

      update journal = new_journal;
      update sync_reqs = pre.sync_reqs.insert(sync_req_id, current_lsn);
    }
  }

  transition! {
    reply_sync(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
    ) {
      let ctam_label = label->ctam_label;
      require ctam_label is ReplySyncOp;

      let sync_req_id = ctam_label.arrow_ReplySyncOp_sync_req_id();
      require pre.sync_reqs.dom().contains(sync_req_id);

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::QueryLsnPersistenceLabel{
          sync_lsn: pre.sync_reqs[sync_req_id],
        }
      );

      update journal = new_journal;
      update sync_reqs = pre.sync_reqs.remove(sync_req_id);
    }
  }

  transition! {
    commit_start(
      label: Label,
      new_boundary_lsn: LSN,
      frozen_journal: MsgHistory,
      frozen_map: StampedMap,
      new_journal: AbstractCrashAwareJournal::State,
      new_mapadt: AbstractCrashAwareMap::State,
    ) {
      let ctam_label = label->ctam_label;
      require ctam_label is Noop;
      require !pre.superblock_in_flight;
      require !pre.superblock_landed;

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::CommitStartLabel {
          new_boundary_lsn: new_boundary_lsn,
          frozen_journal,
        }
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::CommitStartLabel {
          new_boundary_lsn: new_boundary_lsn,
          frozen_map,
        }
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
      update superblock_in_flight = true;
      update superblock_landed = false;

    }
  }

  // This transition models the trusted event of an outstanding superblock write landing on the
  // disk. This event is invisible to the untrusted ("player 2") program, but in the proof we need
  // to model it to precisely identify the linearization point for the Sync transition in the
  // abstract Spec.
  transition! {
    superblock_write_lands(
        label: Label,
    ) {
      let ctam_label = label->ctam_label;
      require ctam_label is SyncOp;
      require pre.superblock_in_flight;
      update superblock_in_flight = false;
      update superblock_landed = true;
    }
  }

  transition! {
    commit_complete(
      label: Label,
      new_mapadt: AbstractCrashAwareMap::State,
      new_journal: AbstractCrashAwareJournal::State,
    ) {
      // The only way we could possibly learn that a commit has completed is if the superblock that
      // was in-flight to the disk landed, since that write reply is the commit-complete
      // notification.
      require pre.superblock_landed;
      require !pre.superblock_in_flight;
      let current_lsn = pre.mapadt.i().seq_end;

      let ctam_label = label->ctam_label;
      require ctam_label is Noop;

      // AbstractCrashAwareJournal commit complete truncates the old
      // part of ephemeral journal that's now saved on disk
      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::CommitCompleteLabel {
          require_end: current_lsn,
        },
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::CommitCompleteLabel,
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
      update superblock_landed = false;
    }
  }

  transition! {
    crash(
      label: Label,
      new_journal: AbstractCrashAwareJournal::State,
      new_mapadt: AbstractCrashAwareMap::State,
    ) {
      // TODO (travis/jonh): Figure out a way to gracefully handle state machines
      // that only have one possible label (or a way to suppress the warning about
      // unreachable branch in `match` statement that these `let` statements expand
      // to)
      // example that triggers the warning:
      // require let Label::Label{ ctam_label } = label;

      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::CrashOp } = label;

      // Tell journal/map whether any frozen state, if present, should be recorded as persistent
      // (because it actually landed on the disk, so the program will find it after recovery) or
      // discarded (because the crash occurred when the superblock was in-flight, so it's lost, so
      // the program will, upon recovery, discover the thing it thought was persistent before the
      // crash step).
      let keep_in_flight = pre.superblock_landed;

      require AbstractCrashAwareJournal::State::next(
        pre.journal,
        new_journal,
        AbstractCrashAwareJournal::Label::CrashLabel{ keep_in_flight }
      );

      require AbstractCrashAwareMap::State::next(
        pre.mapadt,
        new_mapadt,
        AbstractCrashAwareMap::Label::CrashLabel{ keep_in_flight }
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
      update progress = AsyncMap::State::init_ephemeral_state();
      update sync_reqs = Map::empty();

      // The disk I/O buffers are cleared on a crash, which would include any in-flight superblock
      // writes. We must be able to assume this; otherwise, ancient zombie writes could rise from
      // the earth to corrupt future behavior.
      update superblock_in_flight = false;
      update superblock_landed = false;
    }
  }
}

}
}
