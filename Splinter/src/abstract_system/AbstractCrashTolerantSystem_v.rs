// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
/// AbstractCrashTolerantSystem. Formerly named AbstractCoordinationSystem.
/// Coordinates a map and a journal to present a unified map once abstracted.
///
/// This is the final refinement layer before the top level trusted spec.

use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;

use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::*;

use crate::abstract_system::AbstractCrashAwareJournal_v::*;
use crate::abstract_system::AbstractCrashAwareMap_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};

// TODO (jonh): Rename all of the labels in all files to exclude "Op" or "Label" since it's redundant
// as enums are already namespaced under "Label", so it's like saying "Label Label"

verus! {

/// SyncReqId's are used to assign sync requests unique IDs. Actual value is meaningless beyond
/// identifying a specific sync request.
type SyncReqId = nat;

/// SyncReqs represents a set of outstanding sync requests. Sync requests are stored as key-value
/// pairs: (key, map_lsn), where "key" is the sync request ID, and "map_lsn" was the last executed
/// LSN on the map at the time the sync request was made.
type SyncReqs = Map<SyncReqId, LSN>;

/// The ephemeral state of the Coordination Layer (when known).
pub struct Known {
  /// Tracks the set of outstanding client requests and undelivered replies. See MapSpec_t::EphemeralState.
  pub progress: MapSpec_t::EphemeralState,
  /// The set of outstanding sync requests.
  pub sync_reqs: SyncReqs,
  /// The LSN one past the end of 
  pub map_lsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
}

/// Ephemeral state for coordination layer can be known or unknown. The ephemeral
/// state is known if the Option type is Some, and unknown if the Option type is
/// None.
type Ephemeral = Option<Known>;

state_machine!{ CoordinationSystem {
  fields {
    /// The state of the journal in our system.
    pub journal: CrashTolerantJournal::State,
    /// State of the map backing our system.
    pub mapadt: CrashTolerantMap::State,
    /// The ephemeral state of the coordination system tracks the outstanding
    /// requests and replies for map operations, as well as the set of outstanding
    /// sync requests. Invariant: if not Known, then we cannot accept new requests
    /// (represents that our in-memory state has crashed and isn't fully up to date
    /// with persistent information yet).
    pub ephemeral: Ephemeral,
  }

  // Labels of coordinationsystem should directly be the labels of the
  // CrashTolerantAsyncMap labels. Ideal would be to just copy it somehow,
  // but for now we're just wrapping the CTAM ones.
  pub enum Label{
    Label{ ctam_label: CrashTolerantAsyncMap::Label }
  }

  init! {
    // Raise the non-determinism to the caller level (functional style)
    // initialize(j: CrashTolerantJournal::State, m: CrashTolerantMap::State) {
    //   require CrashTolerantJournal::State::initialize(j);
    //   require CrashTolerantMap::State::initialize(m)
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
      require CrashTolerantJournal::State::init(state.journal);
      require CrashTolerantMap::State::init(state.mapadt);
      init journal = state.journal;
      init mapadt = state.mapadt;
      init ephemeral = None;
    }
  }

  transition! {
    // Load the state of the ephemeral journal and map from the persistent
    // state (just a direct copy)
    load_ephemeral_from_persistent(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
      map_lsn: LSN,
    ) {
      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::Noop } = label;
      
      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::LoadEphemeralFromPersistentLabel
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::LoadEphemeralFromPersistentLabel{ end_lsn: map_lsn }
      );

      // Solving the "initial" state problem is weird. Inherently we want a function
      // that returns a non-deterministic value, but as we've noted: not really possible
      // What would that primitive even be? An amorphous blob?

      update ephemeral = Some(
        Known {
          progress: AsyncMap::State::init_ephemeral_state(),
          sync_reqs: Map::empty(),
          map_lsn: map_lsn,
        }
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
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
      records: MsgHistory,
    ) {
      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::Noop } = label;

      require pre.ephemeral is Some;
      require records.wf();

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::ReadForRecoveryLabel{ records }
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::PutRecordsLabel{ records }
      );

      update ephemeral = Some(
        Known {
          map_lsn: records.seq_end,
          ..pre.ephemeral.get_Some_0()
        }
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
      require pre.ephemeral is Some;

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
      // require pre.ephemeral is Some;
      // let pre_ephemeral = pre.ephemeral.get_Some_0();
      // require ctam_label is OperateOp;
      // let base_op = ctam_label.get_OperateOp_base_op();
      // require base_op is RequestOp;
      // let req = base_op.get_RequestOp_req();

      require !pre.ephemeral.get_Some_0().progress.requests.contains(req);

      // Wanted to do something like this but not available
      // let mut new_ephemeral = pre.ephemeral;
      // new_ephemeral.get_Some_0().progress.requests =
      //   new_ephemeral.get_Some_0().progress.requests + req;

      // This is ugly
      // IDEAL SYNTAX:
      // update ephemeral.unwrap().progress.requests = @.insert(req);
      update ephemeral = Some(
        Known{
          progress: MapSpec_t::EphemeralState{
            requests: pre.ephemeral.get_Some_0().progress.requests.insert(req),
            ..pre.ephemeral.get_Some_0().progress
          },
          ..pre.ephemeral.get_Some_0()
        }
      );
    }
  }

  transition! {
    // Execute a previously requested query on the kv-store.
    query(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
    ) {
      // State must be known
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      // The query transition label is labeled with the input and output of the
      // query operation. We want to dissect that information out so that we can
      // require that we only execute a query transition if it corresponds to a
      // previously requested query (as well as assert that enums are of right
      // type along the way). (Unfortunately this requires a series of rather
      // ugly calls).
      let ctam_label = label.get_Label_ctam_label();

      require ctam_label is OperateOp;
      let base_op = ctam_label.get_OperateOp_base_op();
      require base_op is ExecuteOp;
      let req = base_op.get_ExecuteOp_req();
      let reply = base_op.get_ExecuteOp_reply();
      require req.input is QueryInput;
      require reply.output is QueryOutput;
      let key = req.input.get_QueryInput_key();
      let value = reply.output.get_QueryOutput_value();

      require pre_ephemeral.progress.requests.contains(req);
      require req.id == reply.id;

      require !pre_ephemeral.progress.replies.contains(reply);

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::QueryEndLsnLabel{end_lsn: pre_ephemeral.map_lsn},
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::QueryLabel{
          end_lsn: pre_ephemeral.map_lsn,
          key: key,
          value: value,
        },
      );

      // Remove the request from outstanding requests, and add corresponding
      // response to set of undelivered replies.
      update ephemeral = Some(
        Known{
          progress: MapSpec_t::EphemeralState{
            requests: pre_ephemeral.progress.requests.remove(req),
            replies: pre_ephemeral.progress.replies.insert(reply),
          },
          ..pre_ephemeral
        }
      );
      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    put(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

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

      require pre_ephemeral.progress.requests.contains(req);
      require req.id == reply.id;
      require !pre_ephemeral.progress.replies.contains(reply);

      // TODO: let keyed_message = 
      let keyed_message = KeyedMessage{
        key: key,
        message: Message::Define { value: value },
      };
      // TODO: let singleton: MsgHistory = <something>;
      let singleton = MsgHistory::singleton_at(pre_ephemeral.map_lsn, keyed_message);

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::PutLabel{ records: singleton },
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::PutRecordsLabel{ records: singleton },
      );

      update ephemeral = Some(
        Known {
          map_lsn: pre_ephemeral.map_lsn + 1,
          progress: MapSpec_t::EphemeralState{
            requests: pre_ephemeral.progress.requests.remove(req),
            replies: pre_ephemeral.progress.replies.insert(reply),
          },
          ..pre_ephemeral
        }
      );
      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    deliver_reply(label: Label) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();
      
      let ctam_label = label.get_Label_ctam_label();

      require ctam_label is OperateOp;
      
      let base_op = ctam_label.get_OperateOp_base_op();
      require base_op is ReplyOp;

      let reply = base_op.get_ReplyOp_reply();

      require pre_ephemeral.progress.replies.contains(reply);
      update ephemeral = Some(
        Known {
          progress: MapSpec_t::EphemeralState {
            replies: pre_ephemeral.progress.replies.remove(reply),
            ..pre_ephemeral.progress
          },
          ..pre_ephemeral
        }
      );
    }
  }

  transition! {
    journal_internal(
      label: Label,
      new_journal: CrashTolerantJournal::State,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      let ctam_label = label.get_Label_ctam_label();
      require ctam_label is Noop;

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::InternalLabel,
      );

      update journal = new_journal;
    }
  }

  transition! {
    map_internal(
      label: Label,
      new_mapadt: CrashTolerantMap::State,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      let ctam_label = label.get_Label_ctam_label();
      require ctam_label is Noop;

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::InternalLabel,
      );

      update mapadt = new_mapadt;
    }
  }

  transition! {
    req_sync(
      label: Label,
      new_journal: CrashTolerantJournal::State,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      let ctam_label = label.get_Label_ctam_label();
      require ctam_label is ReqSyncOp;

      let sync_req_id = ctam_label.get_ReqSyncOp_sync_req_id();
      require !pre_ephemeral.sync_reqs.dom().contains(sync_req_id);
      
      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::QueryEndLsnLabel{ end_lsn: pre_ephemeral.map_lsn },
      );

      update journal = new_journal;
      update ephemeral = Some(
        Known {
          sync_reqs: pre_ephemeral.sync_reqs.insert(sync_req_id, pre_ephemeral.map_lsn),
          ..pre_ephemeral
        }
      );
    }
  }

  transition! {
    reply_sync(
      label: Label,
      new_journal: CrashTolerantJournal::State,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      let ctam_label = label.get_Label_ctam_label();
      require ctam_label is ReplySyncOp;

      let sync_req_id = ctam_label.get_ReplySyncOp_sync_req_id();
      require pre_ephemeral.sync_reqs.dom().contains(sync_req_id);

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::QueryLsnPersistenceLabel{
          sync_lsn: pre_ephemeral.sync_reqs[sync_req_id],
        }
      );

      update journal = new_journal;
      update ephemeral = Some(
        Known {
          sync_reqs: pre_ephemeral.sync_reqs.remove(sync_req_id),
          ..pre_ephemeral
        }
      );
    }
  }

  transition! {
    commit_start(
      label: Label,
      new_boundary_lsn: LSN,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      let ctam_label = label.get_Label_ctam_label();
      require ctam_label is Noop;

      require CrashTolerantJournal::State::next(
        pre.journal,
        pre.journal,
        CrashTolerantJournal::Label::CommitStartLabel {
          new_boundary_lsn: new_boundary_lsn,
          max_lsn: pre_ephemeral.map_lsn,
        }
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        pre.mapadt,
        CrashTolerantMap::Label::CommitStartLabel {
          new_boundary_lsn: new_boundary_lsn,
        }
      );

      // ephemeral unchanged
    }
  }

  transition! {
    commit_complete(
      label: Label,
      new_mapadt: CrashTolerantMap::State,
      new_journal: CrashTolerantJournal::State,
    ) {
      require pre.ephemeral is Some;
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      let ctam_label = label.get_Label_ctam_label();
      require ctam_label is SyncOp;

      // CrashTolerantJournal commit complete truncates the old
      // part of ephemeral journal that's now saved on disk
      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::CommitCompleteLabel {
          require_end: pre_ephemeral.map_lsn,
        },
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::CommitCompleteLabel,
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
      // ephemeral unchanged
    }
  }

  transition! {
    crash(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
    ) {
      // TODO (travis/jonh): Figure out a way to gracefully handle state machines
      // that only have one possible label (or a way to suppress the warning about
      // unreachable branch in `match` statement that these `let` statements expand
      // to)
      // example that triggers the warning:
      // require let Label::Label{ ctam_label } = label;

      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::CrashOp } = label;

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::CrashLabel
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::CrashLabel
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
      update ephemeral = None;
    }
  }
}

}
}
