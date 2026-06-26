// CrashAwareCachingDiskSystem: a proof-oriented coordination composition of the
// crash-aware caching-disk journal and branch store.
//
// This module deliberately does not project from AtomicState or
// SystemModel<ConcreteProgramModel>. Physical cache/disk projection lives in
// BracketRefinement_v; CrashAwareCachingDiskSystem only coordinates component states.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map_lib::lemma_values_finite;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::AbstractCrashAwareSystem_v::CoordinationSystem;
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v::*;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::implementation::AllocationBranchStackRefinement_v::append_puts;
use crate::allocation_layer::AllocationJournal_v::JournalImage;
use crate::implementation::CachingDiskJournal_v::CachingDiskJournal;
use crate::implementation::CrashAwareAllocationBranchStackRefinement_v::*;
use crate::implementation::CrashAwareAllocationBranchStack_v::FrozenAllocationBranchStack;
use crate::implementation::CrashAwareCachingDiskBranch_v::{
    EphemeralCachingDiskBranch, PersistentCachingDiskBranch, CrashAwareCachingDiskBranch,
};
use crate::implementation::CachingDiskBranch_v::{
    CachingDiskBranch, CachingDiskBranchMetadata, CachingDiskBranchImage,
    empty_caching_disk_branch_image, empty_caching_disk_branch_image_wf,
};
use crate::implementation::CrashAwareCachingDiskBranchRefinement_v::*;
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CachingDiskJournalImage, EphemeralCachingDiskJournal, PersistentCachingDiskJournal,
    CrashAwareCachingDiskJournal, caching_disk_journal_accessible_aus,
};
use crate::implementation::CrashAwareCachingDiskJournalRefinement_v::*;
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot};
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, empty_abstract_superblock_image, superblock_matches,
};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::betree::Utils_v::lemma_union_set_of_sets_contains;
use crate::disk::GenericDisk_v::{Address, AU, to_aus, to_aus_preserves_lte};
use crate::implementation::CachingDisk_v::CachingDiskRawPage as RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{AsyncMap, EphemeralState, Input, Output, Reply, Request, SyncReqId};
use crate::spec::Messages_t::Message;

verus! {

pub open spec fn singleton_key_seq(key: Key) -> Seq<Key>
{
    seq![key]
}

pub open spec fn singleton_message_seq(msg: Message) -> Seq<Message>
{
    seq![msg]
}

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
    pub proof fn inv_next(pre: Self, post: Self, lbl: SuperblockStore::Label)
        requires
            pre.inv(),
            SuperblockStore::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(SuperblockStore::State::next);
        reveal(SuperblockStore::State::next_by);
        let step = choose |step| SuperblockStore::State::next_by(pre, post, lbl, step);
        match step {
            SuperblockStore::Step::write() => {
                reveal(SuperblockStore::State::write);
            },
            SuperblockStore::Step::land() => {
                reveal(SuperblockStore::State::land);
            },
            SuperblockStore::Step::complete() => {
                reveal(SuperblockStore::State::complete);
            },
            SuperblockStore::Step::crash() => {
                reveal(SuperblockStore::State::crash);
            },
            SuperblockStore::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        };
    }
}

state_machine!{ CrashAwareCachingDiskSystem {
    fields {
        pub journal: CrashAwareCachingDiskJournal::State,
        pub branch: CrashAwareCachingDiskBranch::State,
        pub progress: EphemeralState,
        pub sync_reqs: Map<SyncReqId, LSN>,
        pub superblockstore: SuperblockStore::State,
        pub free_aus: Set<AU>,
    }

    pub enum Label {
        Request{ req: Request },
        Execute{ req: Request, reply: Reply },
        Reply{ reply: Reply },
        ReqSync{ sync_req_id: SyncReqId },
        ReplySync{ sync_req_id: SyncReqId },
        Sync,
        Crash,
        Noop,
    }

    init!{ initialize(
        free_aus: Set<AU>,
        initial_superblock: RawPage,
        journal: CrashAwareCachingDiskJournal::State,
        branch: CrashAwareCachingDiskBranch::State,
    ) {
        require Self::reserved_aus().disjoint(free_aus);
        require initial_superblock == Self::empty_superblock_page();
        require CrashAwareCachingDiskJournal::State::initialize(journal);
        require CrashAwareCachingDiskBranch::State::initialize(branch);

        init journal = journal;
        init branch = branch;
        init progress = AsyncMap::State::init_ephemeral_state();
        init sync_reqs = Map::<SyncReqId, LSN>::empty();
        init superblockstore = SuperblockStore::State{
            persistent: initial_superblock,
            in_flight: Option::None,
            landed: false,
        };
        init free_aus = free_aus;
    }}

    transition!{ accept_request(lbl: Label) {
        require let Label::Request{req} = lbl;
        require !pre.progress.requests.contains(req);

        update progress = EphemeralState{
            requests: pre.progress.requests.insert(req),
            ..pre.progress
        };
    }}

    transition!{ deliver_reply(lbl: Label) {
        require let Label::Reply{reply} = lbl;
        require pre.progress.replies.contains(reply);

        update progress = EphemeralState{
            replies: pre.progress.replies.remove(reply),
            ..pre.progress
        };
    }}

    transition!{ query(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require req.input is QueryInput;
        require reply.output is QueryOutput;
        require req.id == reply.id;
        require pre.progress.requests.contains(req);
        require !pre.progress.replies.contains(reply);

        let key = req.input.arrow_QueryInput_key();
        let value = reply.output.arrow_QueryOutput_value();
        require pre.journal.ephemeral is Known;
        require pre.journal.ephemeral->v.journal.status is Some;
        require pre.journal_lsn() == pre.branch_lsn();
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::Query{key, value},
        );

        update branch = new_branch;
        update progress = EphemeralState{
            requests: pre.progress.requests.remove(req),
            replies: pre.progress.replies.insert(reply),
        };
    }}

    transition!{ put(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require let Request{ input: Input::PutInput{key, value}, id: request_id } = req;
        require let Reply{ output: Output::PutOutput, id: reply_id } = reply;
        require request_id == reply_id;
        require pre.progress.requests.contains(req);
        require !pre.progress.replies.contains(reply);

        let msg = Message::Define{value};
        let keyed_message = KeyedMessage{key, message: msg};
        let singleton = MsgHistory::singleton_at(pre.branch_lsn(), keyed_message);

        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Put{records: singleton},
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::Append{
                keys: singleton_key_seq(key),
                msgs: singleton_message_seq(msg),
            },
        );

        update journal = new_journal;
        update branch = new_branch;
        update progress = EphemeralState{
            requests: pre.progress.requests.remove(req),
            replies: pre.progress.replies.insert(reply),
        };
    }}

    transition!{ execute_noop(lbl: Label) {
        require let Label::Execute{req, reply} = lbl;
        require req.input is NoopInput;
        require reply.output is NoopOutput;
        require req.id == reply.id;
        require pre.progress.requests.contains(req);
        require !pre.progress.replies.contains(reply);

        update progress = EphemeralState{
            requests: pre.progress.requests.remove(req),
            replies: pre.progress.replies.insert(reply),
        };
    }}

    transition!{ req_sync(lbl: Label) {
        require let Label::ReqSync{sync_req_id} = lbl;
        require !pre.sync_reqs.dom().contains(sync_req_id);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            pre.journal,
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn: pre.branch_lsn()},
        );

        update sync_reqs = pre.sync_reqs.insert(sync_req_id, pre.branch_lsn());
    }}

    transition!{ reply_sync(lbl: Label) {
        require let Label::ReplySync{sync_req_id} = lbl;
        require pre.sync_reqs.dom().contains(sync_req_id);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            pre.journal,
            CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{
                sync_lsn: pre.sync_reqs[sync_req_id],
            },
        );

        update sync_reqs = pre.sync_reqs.remove(sync_req_id);
    }}

    transition!{ journal_internal(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Internal,
        );

        update journal = new_journal;
    }}

    transition!{ journal_observe_clean_aus(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        aus: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
        );

        update journal = new_journal;
    }}

    transition!{ journal_load_index(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        discovered_aus: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus},
        );

        update journal = new_journal;
        update free_aus = pre.free_aus - discovered_aus;
    }}

    transition!{ journal_internal_alloc(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
    ) {
        require lbl is Noop;
        require allocs <= pre.free_aus;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
        );

        update journal = new_journal;
        update free_aus = (pre.free_aus - allocs) + deallocs;
    }}

    transition!{ map_internal(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::Internal,
        );

        update branch = new_branch;
    }}

    transition!{ component_internals(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Internal,
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::Internal,
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ map_load_metadata(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
        root: Address,
        discovered_aus: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        );
        require discovered_aus <= pre.branch_owned_aus();

        update branch = new_branch;
        update free_aus = pre.free_aus - discovered_aus;
    }}

    transition!{ map_internal_alloc(
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) {
        require lbl is Noop;
        require allocs <= pre.free_aus;
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::InternalAlloc{allocs, deallocs},
        );

        update branch = new_branch;
        update free_aus = (pre.free_aus - allocs) + deallocs;
    }}

    transition!{ load_ephemeral_from_persistent(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::LoadEphemeral,
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::LoadEphemeral,
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ recover(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        records: MsgHistory,
        keys: Seq<Key>,
        msgs: Seq<Message>,
    ) {
        require lbl is Noop;
        require records == append_puts(pre.branch_lsn(), keys, msgs);
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{records},
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs},
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ commit_start(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        superblock_image: AbstractSuperblockImage,
    ) {
        let new_boundary_lsn = superblock_image.branch_seq_end;
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitStart{
                new_boundary_lsn,
                snapshot: superblock_image.journal_snapshot,
                seq_end: superblock_image.journal_seq_end,
            },
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::CommitStart{
                new_boundary_lsn,
                sealed_roots: superblock_image.branch_roots,
            },
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ commit_prepared(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        new_superblock: SuperblockStore::State,
        raw_page: RawPage,
    ) {
        require lbl is Noop;
        require pre.commit_started();
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::FreezePrepared,
        );
        require superblock_matches(raw_page, pre.frozen_superblock_image());
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Write{raw: raw_page},
        );

        update journal = new_journal;
        update branch = new_branch;
        update superblockstore = new_superblock;
    }}

    transition!{ superblock_write_lands(
        lbl: Label,
        new_superblock: SuperblockStore::State,
    ) {
        require lbl is Sync;
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Land,
        );

        update superblockstore = new_superblock;
    }}

    transition!{ commit_complete(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        new_superblock: SuperblockStore::State,
        discarded: Set<AU>,
    ) {
        require lbl is Noop;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::CommitComplete{
                require_end: pre.branch_lsn(),
                discarded,
            },
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::CommitComplete,
        );
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Complete,
        );

        update journal = new_journal;
        update branch = new_branch;
        update superblockstore = new_superblock;
        update free_aus = pre.free_aus + discarded;
    }}

    transition!{ crash(
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        new_superblock: SuperblockStore::State,
        keep_in_flight: bool,
    ) {
        require lbl is Crash;
        require keep_in_flight == pre.superblockstore.landed;
        require CrashAwareCachingDiskJournal::State::next(
            pre.journal,
            new_journal,
            CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight},
        );
        require CrashAwareCachingDiskBranch::State::next(
            pre.branch,
            new_branch,
            CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight},
        );
        require SuperblockStore::State::next(
            pre.superblockstore,
            new_superblock,
            SuperblockStore::Label::Crash,
        );

        update journal = new_journal;
        update branch = new_branch;
        update superblockstore = new_superblock;
        update progress = AsyncMap::State::init_ephemeral_state();
        update sync_reqs = Map::empty();
        update free_aus = Set::empty();
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Noop;
    }}

    pub open spec fn components_wf(self) -> bool
    {
        &&& self.journal.inv()
        &&& self.branch.inv()
    }

    pub open spec fn components_loaded_agree(self) -> bool
    {
        (self.journal.ephemeral is Known) == (self.branch.ephemeral is Known)
    }

    pub open spec fn journal_lsn(self) -> LSN
    {
        if self.journal.ephemeral is Known && self.journal.ephemeral->v.journal.status is Some {
            self.journal.ephemeral->v.journal.seq_end()
        } else {
            self.journal.persistent.metadata().seq_end
        }
    }

    pub open spec fn journal_state_owned_aus(journal: CrashAwareCachingDiskJournal::State) -> Set<AU>
    {
        let ephemeral_aus = if journal.ephemeral is Known {
            caching_disk_journal_accessible_aus(journal.ephemeral->v)
        } else {
            Set::empty()
        };
        let persistent_aus = if journal.ephemeral is Unknown && journal.persistent is Image {
            journal.persistent->image.accessible_aus()
        } else {
            Set::empty()
        };
        persistent_aus + ephemeral_aus
    }

    pub open spec fn journal_owned_aus(self) -> Set<AU>
    {
        Self::journal_state_owned_aus(self.journal)
    }

    pub open spec fn branch_state_owned_aus(branch: CrashAwareCachingDiskBranch::State) -> Set<AU>
    {
        let ephemeral_aus = if branch.ephemeral is Known {
            branch.ephemeral->v.full_accessible_aus()
        } else {
            Set::empty()
        };
        let persistent_aus = if branch.ephemeral is Unknown && branch.persistent is Image {
            to_aus(branch.persistent->image.persistent.dom())
                + summary_aus(branch.persistent->image.branch_summary())
        } else {
            Set::empty()
        };
        persistent_aus + ephemeral_aus
    }

    pub open spec fn branch_owned_aus(self) -> Set<AU>
    {
        Self::branch_state_owned_aus(self.branch)
    }

    pub open spec fn component_owned_aus(self) -> Set<AU>
    {
        Self::reserved_aus() + self.journal_owned_aus() + self.branch_owned_aus()
    }

    pub open spec fn component_disjoint(self) -> bool
    {
        &&& Self::reserved_aus().disjoint(self.journal_owned_aus())
        &&& Self::reserved_aus().disjoint(self.branch_owned_aus())
        &&& self.journal_owned_aus().disjoint(self.branch_owned_aus())
    }

    pub open spec fn allocation_wf(self) -> bool
    {
        &&& self.free_aus.disjoint(self.component_owned_aus())
        &&& self.component_disjoint()
    }

    pub open spec fn commit_started(self) -> bool
    {
        self.journal.frozen is Some && self.branch.frozen is Some
    }

    pub open spec fn frozen_superblock_image(self) -> AbstractSuperblockImage
    {
        if self.commit_started() {
            AbstractSuperblockImage{
                journal_snapshot: self.journal.frozen.unwrap().snapshot,
                journal_seq_end: self.journal.frozen.unwrap().seq_end,
                branch_roots: self.branch.frozen.unwrap().sealed_roots,
                branch_seq_end: self.branch.frozen.unwrap().seq_end,
            }
        } else {
            empty_abstract_superblock_image()
        }
    }

    pub open spec fn superblock_commit_wf(self) -> bool
    {
        &&& self.superblockstore.in_flight is Some ==> self.commit_started()
        &&& self.superblockstore.landed ==> self.commit_started()
        &&& self.superblockstore.in_flight is Some ==> self.journal.prepared
        &&& self.superblockstore.landed ==> self.journal.prepared
        &&& self.superblockstore.in_flight is Some ==> self.branch.prepared
        &&& self.superblockstore.landed ==> self.branch.prepared
    }

    #[invariant]
    pub open spec fn inv(self) -> bool
    {
        &&& self.components_wf()
        &&& self.components_loaded_agree()
        &&& self.superblockstore.inv()
        &&& self.allocation_wf()
        &&& self.superblock_commit_wf()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(
        post: Self,
        free_aus: Set<AU>,
        initial_superblock: RawPage,
        journal: CrashAwareCachingDiskJournal::State,
        branch: CrashAwareCachingDiskBranch::State,
    ) {
        reveal(CrashAwareCachingDiskJournal::State::initialize);
        JournalImage::empty_is_valid_image();
        assert(journal.persistent is Image);
        assert(journal.persistent->image == CachingDiskJournalImage::empty());
        assert(journal.persistent->image.i() == JournalImage::empty());
        assert(journal.persistent->image.wf());
        assert(journal.inv());
        journal.init_refines();
        reveal(CrashAwareCachingDiskBranch::State::initialize);
        empty_caching_disk_branch_image_wf();
        assert(branch.persistent == PersistentCachingDiskBranch::Image{
            image: empty_caching_disk_branch_image(),
        });
        branch.init_refines();
        assert(post.journal_owned_aus() == Set::<AU>::empty());
        assert(post.branch_owned_aus() == Set::<AU>::empty()) by {
            let image = branch.persistent->image;
            assert(image.branch_summary() == Map::<AU, Set<AU>>::empty());
            assert(summary_aus(image.branch_summary()) =~= Set::<AU>::empty()) by {
                lemma_values_finite(image.branch_summary());
                assert forall |au: AU| #[trigger] summary_aus(image.branch_summary()).contains(au)
                    implies false by {
                    let s = lemma_union_set_of_sets_contains(
                        image.branch_summary().values(),
                        au,
                    );
                    assert(image.branch_summary().values().contains(s));
                    assert(false);
                }
            };
        }
        assert(post.free_aus.disjoint(post.component_owned_aus()));
        assert(post.component_disjoint());
        assert(!post.commit_started());
        assert(post.superblock_commit_wf());
    }

    #[inductive(accept_request)]
    fn accept_request_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(deliver_reply)]
    fn deliver_reply_inductive(pre: Self, post: Self, lbl: Label) {}

    proof fn branch_owned_aus_ephemeral_growth(
        pre_branch: CrashAwareCachingDiskBranch::State,
        post_branch: CrashAwareCachingDiskBranch::State,
        growth: Set<AU>,
    )
        requires
            post_branch.persistent == pre_branch.persistent,
            post_branch.frozen == pre_branch.frozen,
            post_branch.prepared == pre_branch.prepared,
            post_branch.ephemeral is Known,
            pre_branch.ephemeral is Known,
            post_branch.ephemeral->v.full_accessible_aus()
                <= pre_branch.ephemeral->v.full_accessible_aus() + growth,
        ensures
            Self::branch_state_owned_aus(post_branch)
                <= Self::branch_state_owned_aus(pre_branch) + growth,
    {
        assert forall |au: AU| #[trigger] Self::branch_state_owned_aus(post_branch).contains(au)
            implies (Self::branch_state_owned_aus(pre_branch) + growth).contains(au) by {
            if post_branch.ephemeral->v.full_accessible_aus().contains(au) {
                assert((pre_branch.ephemeral->v.full_accessible_aus() + growth).contains(au));
            }
        };
    }

    proof fn branch_owned_aus_ephemeral_subset(
        pre_branch: CrashAwareCachingDiskBranch::State,
        post_branch: CrashAwareCachingDiskBranch::State,
    )
        requires
            post_branch.persistent == pre_branch.persistent,
            post_branch.frozen == pre_branch.frozen,
            post_branch.prepared == pre_branch.prepared,
            post_branch.ephemeral is Known,
            pre_branch.ephemeral is Known,
            post_branch.ephemeral->v.full_accessible_aus()
                <= pre_branch.ephemeral->v.full_accessible_aus(),
        ensures
            Self::branch_state_owned_aus(post_branch)
                <= Self::branch_state_owned_aus(pre_branch),
    {
        Self::branch_owned_aus_ephemeral_growth(pre_branch, post_branch, Set::<AU>::empty());
    }

    #[inductive(query)]
    fn query_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        match lbl {
            Label::Execute{req, reply} => {
                let key = req.input.arrow_QueryInput_key();
                let value = reply.output.arrow_QueryOutput_value();
                let branch_lbl = CrashAwareCachingDiskBranch::Label::Query{key, value};
                CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
                Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
                assert(new_branch == pre.branch) by {
                    reveal(CrashAwareCachingDiskBranch::State::next);
                    reveal(CrashAwareCachingDiskBranch::State::next_by);
                    let step = choose |step: CrashAwareCachingDiskBranch::Step|
                        CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
                    match step {
                        CrashAwareCachingDiskBranch::Step::query(msg) => {
                            reveal(CrashAwareCachingDiskBranch::State::query);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                }
                assert(post.journal == pre.journal);
                assert(post.branch == pre.branch);
                assert(post.free_aus == pre.free_aus);
                assert(post.component_owned_aus() == pre.component_owned_aus());
                Self::allocation_wf_from_subset(pre, post);
            },
            _ => { }
        }
    }

    #[inductive(put)]
    fn put_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        match lbl {
            Label::Execute{req, reply} => {
                match req.input {
                    Input::PutInput{key, value} => {
                        let msg = Message::Define{value};
                        let keyed_message = KeyedMessage{key, message: msg};
                        let singleton = MsgHistory::singleton_at(pre.branch_lsn(), keyed_message);
                        let journal_lbl = CrashAwareCachingDiskJournal::Label::Put{records: singleton};
                        let branch_lbl = CrashAwareCachingDiskBranch::Label::Append{
                            keys: singleton_key_seq(key),
                            msgs: singleton_message_seq(msg),
                        };
                        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
                        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
                        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
                        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
                        assert(CrashAwareCachingDiskJournal::State::put(
                            pre.journal,
                            new_journal,
                            journal_lbl,
                            new_journal.ephemeral->v,
                        )) by {
                            reveal(CrashAwareCachingDiskJournal::State::next);
                            reveal(CrashAwareCachingDiskJournal::State::next_by);
                            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
                            match step {
                                CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {},
                                _ => { assert(false); },
                            }
                        }
                        if pre.journal.ephemeral is Known {
                            let old_e = pre.journal.ephemeral->v;
                            let new_e = new_journal.ephemeral->v;
                            let cj_lbl = CachingDiskJournal::Label::Put{messages: singleton};
                            assert(CachingDiskJournal::State::next(old_e, new_e, cj_lbl));
	                            assert(new_e.disk == old_e.disk
	                                && new_e.mini_allocator == old_e.mini_allocator) by {
	                                reveal(CachingDiskJournal::State::next);
	                                reveal(CachingDiskJournal::State::next_by);
	                                let step = choose |step: CachingDiskJournal::Step|
	                                    CachingDiskJournal::State::next_by(old_e, new_e, cj_lbl, step);
	                                match step {
	                                    CachingDiskJournal::Step::put(new_cached_journal) => {
	                                        assert(CachingDiskJournal::State::put(old_e, new_e, cj_lbl, new_cached_journal));
	                                        CachedJournal::State::put_effect(old_e.journal, new_e.journal, singleton);
	                                    },
	                                    _ => { assert(false); },
	                                }
	                            }
	                            assert(CachedJournal::State::next(
	                                old_e.journal,
	                                new_e.journal,
	                                CachedJournal::Label::Put{messages: singleton},
	                            )) by {
	                                reveal(CachingDiskJournal::State::next);
	                                reveal(CachingDiskJournal::State::next_by);
	                                let step = choose |step: CachingDiskJournal::Step|
	                                    CachingDiskJournal::State::next_by(old_e, new_e, cj_lbl, step);
	                                match step {
	                                    CachingDiskJournal::Step::put(new_cached_journal) => {
	                                        assert(CachingDiskJournal::State::put(old_e, new_e, cj_lbl, new_cached_journal));
	                                    },
	                                    _ => { assert(false); },
	                                }
	                            }
	                            CachedJournal::State::put_effect(old_e.journal, new_e.journal, singleton);
	                            assert(new_e.lsn_au_index_or_empty() =~= old_e.lsn_au_index_or_empty());
	                            assert(caching_disk_journal_accessible_aus(new_e)
	                                =~= caching_disk_journal_accessible_aus(old_e));
                        }
                        assert(CrashAwareCachingDiskBranch::State::append(
                            pre.branch,
                            new_branch,
                            branch_lbl,
                            new_branch.ephemeral->v,
                        )) by {
                            reveal(CrashAwareCachingDiskBranch::State::next);
                            reveal(CrashAwareCachingDiskBranch::State::next_by);
                            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
                            match step {
                                CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {},
                                _ => { assert(false); },
                            }
                        }
                        if pre.branch.ephemeral is Known {
                            assert(new_branch.ephemeral is Known);
                            let old_b = pre.branch.ephemeral->v;
                            let new_b = new_branch.ephemeral->v;
                            let cb_lbl = CachingDiskBranch::Label::AppendLabel{
                                keys: singleton_key_seq(key),
                                msgs: singleton_message_seq(msg),
                            };
                            assert(CachingDiskBranch::State::next(old_b, new_b, cb_lbl));
                            CachingDiskBranch::State::append_preserves_accessible_aus(
                                old_b,
                                new_b,
                                cb_lbl,
                            );
                            old_b.metadata_loaded_full_accessible_eq();
                            new_b.metadata_loaded_full_accessible_eq();
                            assert(new_b.full_accessible_aus() <= old_b.full_accessible_aus());
                        }
                        assert(post.free_aus == pre.free_aus);
                        assert(Self::journal_state_owned_aus(post.journal)
                            <= Self::journal_state_owned_aus(pre.journal));
                        Self::branch_owned_aus_ephemeral_subset(pre.branch, post.branch);
                        assert(Self::branch_state_owned_aus(post.branch)
                            <= Self::branch_state_owned_aus(pre.branch));
                        assert(post.component_owned_aus() <= pre.component_owned_aus());
                        Self::allocation_wf_from_subset(pre, post);
                    },
                    _ => { }
                }
            },
            _ => { }
        }
    }

    #[inductive(execute_noop)]
    fn execute_noop_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(req_sync)]
    fn req_sync_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
    ) {
    }

    #[inductive(reply_sync)]
    fn reply_sync_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
    ) {
    }

    #[inductive(journal_internal)]
    fn journal_internal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::Internal;
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        assert(CrashAwareCachingDiskJournal::State::internal(
            pre.journal,
            new_journal,
            journal_lbl,
            new_journal.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.journal.ephemeral is Known {
            let old_e = pre.journal.ephemeral->v;
            let new_e = new_journal.ephemeral->v;
            assert(CachingDiskJournal::State::next(old_e, new_e, CachingDiskJournal::Label::Internal));
            CachingDiskJournal::State::internal_preserves_accessible_aus(old_e, new_e);
        }
        assert(post.free_aus == pre.free_aus);
        assert(post.branch == pre.branch);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(journal_observe_clean_aus)]
    fn journal_observe_clean_aus_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        aus: Set<AU>,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus};
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        assert(CrashAwareCachingDiskJournal::State::observe_clean_aus(
            pre.journal,
            new_journal,
            journal_lbl,
            new_journal.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.journal.ephemeral is Known {
            let old_e = pre.journal.ephemeral->v;
            let new_e = new_journal.ephemeral->v;
            let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
            assert(CachingDiskJournal::State::next(old_e, new_e, cj_lbl));
            assert(new_e.accessible_aus() =~= old_e.accessible_aus()) by {
                reveal(CachingDiskJournal::State::next);
                reveal(CachingDiskJournal::State::next_by);
                let step = choose |step: CachingDiskJournal::Step|
                    CachingDiskJournal::State::next_by(old_e, new_e, cj_lbl, step);
                match step {
                    CachingDiskJournal::Step::observe_clean_aus(new_cached_journal) => {
                        assert(CachingDiskJournal::State::observe_clean_aus(
                            old_e,
                            new_e,
                            cj_lbl,
                            new_cached_journal,
                        ));
                        reveal(CachingDiskJournal::State::observe_clean_aus);
                        CachedJournal::State::observe_clean_aus_effect(
                            old_e.journal,
                            new_e.journal,
                            aus,
                        );
                    },
                    _ => { assert(false); },
                }
            }
        }
        assert(post.free_aus == pre.free_aus);
        assert(post.branch == pre.branch);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(journal_load_index)]
    fn journal_load_index_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        discovered_aus: Set<AU>,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus};
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        assert(CrashAwareCachingDiskJournal::State::load_index(
            pre.journal,
            new_journal,
            journal_lbl,
            new_journal.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        assert(post.journal == new_journal);
        assert(post.branch == pre.branch);
        assert(post.free_aus == pre.free_aus - discovered_aus);
        assert(post.journal.persistent == pre.journal.persistent);
        assert(post.journal.frozen == pre.journal.frozen);
        if pre.journal.ephemeral is Known {
            assert(post.journal.ephemeral is Known);
            let old_e = pre.journal.ephemeral->v;
            let new_e = post.journal.ephemeral->v;
            let cj_lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
            assert(CachingDiskJournal::State::next(old_e, new_e, cj_lbl));
            assert(new_e.disk == old_e.disk
                && new_e.mini_allocator == old_e.mini_allocator) by {
                reveal(CachingDiskJournal::State::next);
                reveal(CachingDiskJournal::State::next_by);
                let step = choose |step: CachingDiskJournal::Step|
                    CachingDiskJournal::State::next_by(old_e, new_e, cj_lbl, step);
	                match step {
	                    CachingDiskJournal::Step::load_index(new_cached_journal, reads) => {
	                        assert(CachingDiskJournal::State::load_index(old_e, new_e, cj_lbl, new_cached_journal, reads));
	                        CachedJournal::State::load_index_effect(
	                            old_e.journal,
	                            new_e.journal,
	                            to_journal_records(reads),
	                            discovered_aus,
	                        );
	                    },
	                    _ => { assert(false); },
	                }
	            }
	            reveal(CachingDiskJournal::State::next);
	            reveal(CachingDiskJournal::State::next_by);
	            let load_step = choose |step: CachingDiskJournal::Step|
	                CachingDiskJournal::State::next_by(old_e, new_e, cj_lbl, step);
	            match load_step {
	                CachingDiskJournal::Step::load_index(new_cached_journal, reads) => {
	                    assert(CachingDiskJournal::State::load_index(old_e, new_e, cj_lbl, new_cached_journal, reads));
	                    CachedJournal::State::load_index_effect(
	                        old_e.journal,
	                        new_e.journal,
	                        to_journal_records(reads),
	                        discovered_aus,
	                    );
	                },
	                _ => { assert(false); },
	            }
	            assert(new_e.journal.snapshot == old_e.journal.snapshot);
	            assert(new_e.journal_tj() == old_e.journal_tj());
	            CachingDiskJournal::State::load_index_preserves_accessible_aus(
	                old_e,
	                new_e,
	                discovered_aus,
	            );
	        }
        assert(Self::journal_state_owned_aus(post.journal)
            <= Self::journal_state_owned_aus(pre.journal));
        assert(Self::branch_state_owned_aus(post.branch)
            <= Self::branch_state_owned_aus(pre.branch));
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(journal_internal_alloc)]
    fn journal_internal_alloc_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        assert(CrashAwareCachingDiskJournal::State::internal_alloc(
            pre.journal,
            new_journal,
            journal_lbl,
            new_journal.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.journal.ephemeral is Known {
            let old_e = pre.journal.ephemeral->v;
            let new_e = new_journal.ephemeral->v;
            let cj_lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
            assert(CachingDiskJournal::State::next(old_e, new_e, cj_lbl));
            CachingDiskJournal::State::internal_alloc_accessible_aus(
                old_e,
                new_e,
                allocs,
                deallocs,
                prune_aus,
            );
        }
        assert(post.journal == new_journal);
        assert(post.branch == pre.branch);
        assert(post.free_aus <= (pre.free_aus - allocs) + deallocs);
        assert(allocs <= pre.free_aus);
        assert(post.journal.persistent == pre.journal.persistent);
        assert(post.journal.frozen == pre.journal.frozen);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus() + allocs);
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        assert(deallocs <= pre.journal_owned_aus());
        assert(deallocs.disjoint(post.journal_owned_aus())) by {
            assert(post.journal.ephemeral is Known);
            let new_e = post.journal.ephemeral->v;
            assert(deallocs.disjoint(caching_disk_journal_accessible_aus(new_e)));
            assert forall |au: AU| #[trigger] deallocs.contains(au)
                implies !post.journal_owned_aus().contains(au) by {
                if post.journal_owned_aus().contains(au) {
                    assert(caching_disk_journal_accessible_aus(new_e).contains(au));
                    assert(false);
                }
            }
        };
        assert(deallocs.disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] deallocs.contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                    assert(pre.branch_owned_aus().contains(au));
                    assert(false);
                }
            }
        };
        assert(deallocs.disjoint(Self::reserved_aus())) by {
            assert forall |au: AU| #[trigger] deallocs.contains(au)
                implies !Self::reserved_aus().contains(au) by {
                if Self::reserved_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                    assert(pre.component_owned_aus().contains(au));
                    assert(false);
                }
            }
        };
        assert(deallocs.disjoint(post.component_owned_aus()));
        Self::allocation_wf_from_alloc_update(
            pre,
            post,
            allocs,
            Set::empty(),
            deallocs,
        );
    }

    #[inductive(map_internal)]
    fn map_internal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        let branch_lbl = CrashAwareCachingDiskBranch::Label::Internal;
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskBranch::State::internal(
            pre.branch,
            new_branch,
            branch_lbl,
            new_branch.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.branch.ephemeral is Known {
            let old_b = pre.branch.ephemeral->v;
            let new_b = new_branch.ephemeral->v;
            assert(CachingDiskBranch::State::next(old_b, new_b, CachingDiskBranch::Label::Internal));
            CachingDiskBranch::State::internal_preserves_accessible_aus(old_b, new_b);
            CachingDiskBranch::State::internal_preserves_full_accessible_aus(old_b, new_b);
            assert(new_b.full_accessible_aus() <= old_b.full_accessible_aus());
        }
        assert(post.free_aus == pre.free_aus);
        assert(post.journal == pre.journal);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        Self::branch_owned_aus_ephemeral_subset(pre.branch, post.branch);
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(component_internals)]
    fn component_internals_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::Internal;
        let branch_lbl = CrashAwareCachingDiskBranch::Label::Internal;
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskJournal::State::internal(
            pre.journal,
            new_journal,
            journal_lbl,
            new_journal.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        assert(CrashAwareCachingDiskBranch::State::internal(
            pre.branch,
            new_branch,
            branch_lbl,
            new_branch.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.journal.ephemeral is Known {
            let old_e = pre.journal.ephemeral->v;
            let new_e = new_journal.ephemeral->v;
            assert(CachingDiskJournal::State::next(old_e, new_e, CachingDiskJournal::Label::Internal));
            CachingDiskJournal::State::internal_preserves_accessible_aus(old_e, new_e);
        }
        if pre.branch.ephemeral is Known {
            let old_b = pre.branch.ephemeral->v;
            let new_b = new_branch.ephemeral->v;
            assert(CachingDiskBranch::State::next(old_b, new_b, CachingDiskBranch::Label::Internal));
            CachingDiskBranch::State::internal_preserves_accessible_aus(old_b, new_b);
            CachingDiskBranch::State::internal_preserves_full_accessible_aus(old_b, new_b);
            assert(new_b.full_accessible_aus() <= old_b.full_accessible_aus());
        }
        assert(post.free_aus == pre.free_aus);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        Self::branch_owned_aus_ephemeral_subset(pre.branch, post.branch);
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(map_load_metadata)]
    fn map_load_metadata_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
        root: Address,
        discovered_aus: Set<AU>,
    ) {
        let branch_lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        CrashAwareCachingDiskBranch::State::load_metadata_preserves_full_accessible_aus(
            pre.branch,
            new_branch,
            root,
            discovered_aus,
        );
        CrashAwareCachingDiskBranch::State::load_metadata_accessible_aus_growth(
            pre.branch,
            new_branch,
            root,
            discovered_aus,
        );
        assert(CrashAwareCachingDiskBranch::State::load_metadata(
            pre.branch,
            new_branch,
            branch_lbl,
            new_branch.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        reveal(CrashAwareCachingDiskBranch::State::load_metadata);
        assert(post.free_aus == pre.free_aus - discovered_aus);
        assert(post.journal == pre.journal);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        assert(post.branch == new_branch);
        assert(new_branch.persistent == pre.branch.persistent);
        assert(new_branch.frozen == pre.branch.frozen);
        assert(new_branch.prepared == pre.branch.prepared);
        if pre.branch.ephemeral is Known {
            assert(new_branch.ephemeral is Known);
            assert(new_branch.ephemeral->v.full_accessible_aus()
                == pre.branch.ephemeral->v.full_accessible_aus());
            Self::branch_owned_aus_ephemeral_subset(pre.branch, new_branch);
        }
        assert(post.branch_owned_aus() <= pre.branch_owned_aus() + discovered_aus);
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(map_internal_alloc)]
    fn map_internal_alloc_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_branch: CrashAwareCachingDiskBranch::State,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) {
        let branch_lbl = CrashAwareCachingDiskBranch::Label::InternalAlloc{allocs, deallocs};
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskBranch::State::internal_alloc(
            pre.branch,
            new_branch,
            branch_lbl,
            new_branch.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.branch.ephemeral is Known {
            let old_b = pre.branch.ephemeral->v;
            let new_b = new_branch.ephemeral->v;
            let cb_lbl = CachingDiskBranch::Label::InternalAlloc{allocs, deallocs};
            assert(CachingDiskBranch::State::next(old_b, new_b, cb_lbl));
            CachingDiskBranch::State::internal_alloc_accessible_aus(
                old_b,
                new_b,
                allocs,
                deallocs,
            );
            CachingDiskBranch::State::internal_alloc_full_accessible_aus(
                old_b,
                new_b,
                allocs,
                deallocs,
            );
            assert(new_b.full_accessible_aus() <= old_b.full_accessible_aus() + allocs);
        }
        assert(deallocs == Set::<AU>::empty());
        assert(post.free_aus <= (pre.free_aus - allocs) + deallocs);
        assert(allocs <= pre.free_aus);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        Self::branch_owned_aus_ephemeral_growth(pre.branch, post.branch, allocs);
        assert(post.branch_owned_aus() <= pre.branch_owned_aus() + allocs);
        Self::allocation_wf_from_alloc_update(
            pre,
            post,
            Set::empty(),
            allocs,
            deallocs,
        );
    }

    #[inductive(load_ephemeral_from_persistent)]
    fn load_ephemeral_from_persistent_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
    ) {
        let branch_lbl = CrashAwareCachingDiskBranch::Label::LoadEphemeral;
        let journal_lbl = CrashAwareCachingDiskJournal::Label::LoadEphemeral;
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        assert(CrashAwareCachingDiskJournal::State::load_ephemeral(pre.journal, new_journal, journal_lbl)) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::load_ephemeral() => {},
                _ => { assert(false); },
            }
        }
        assert(CrashAwareCachingDiskBranch::State::load_ephemeral(
            pre.branch,
            new_branch,
            branch_lbl,
            new_branch.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        let journal_image = pre.journal.persistent->image;
        let loaded_journal = CachingDiskJournal::State::load_from_persistent(
            journal_image.snapshot,
            journal_image.persistent,
        );
        CachingDiskJournal::State::load_from_persistent_accessible_aus(
            journal_image.snapshot,
            journal_image.persistent,
        );
        CachingDiskBranch::State::load_from_persistent_accessible_aus(
            pre.branch.persistent->image,
        );
        reveal(CrashAwareCachingDiskJournal::State::load_ephemeral);
        reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
        assert(new_journal.persistent == PersistentCachingDiskJournal::Metadata{
            meta: journal_image.metadata(),
        });
        assert(new_journal.frozen == pre.journal.frozen);
        assert(new_journal.prepared == pre.journal.prepared);
        assert(new_journal.ephemeral is Known);
        assert(new_journal.ephemeral->v == CachingDiskJournal::State::load_from_persistent(
            pre.journal.persistent->image.snapshot,
            pre.journal.persistent->image.persistent,
        ));
        assert(CachingDiskBranch::State::initialize(
            new_branch.ephemeral->v,
            pre.branch.persistent->image,
        ));
        reveal(CachingDiskBranch::State::initialize);
        assert(new_branch.persistent == PersistentCachingDiskBranch::Metadata{
            meta: pre.branch.persistent->image.metadata(),
        });
        assert(new_branch.frozen == pre.branch.frozen);
        assert(new_branch.prepared == pre.branch.prepared);
        assert(new_branch.ephemeral is Known);
        assert(new_branch.ephemeral->v == CachingDiskBranch::State::load_from_persistent(
            pre.branch.persistent->image,
        ));
        assert(post.free_aus <= pre.free_aus) by {
            assert forall |au: AU| #[trigger] post.free_aus.contains(au)
                implies pre.free_aus.contains(au) by {
                assert(pre.free_aus.contains(au));
            }
        };
        assert(post.journal == new_journal);
        assert(post.branch == new_branch);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.journal_owned_aus().contains(au)
                implies pre.journal_owned_aus().contains(au) by {
                if new_journal.ephemeral->v.accessible_aus().contains(au) {
                    assert(CachingDiskJournal::State::load_from_persistent(
                        pre.journal.persistent->image.snapshot,
                        pre.journal.persistent->image.persistent,
                    ).accessible_aus().contains(au));
                    assert(to_aus(pre.journal.persistent->image.persistent.dom()).contains(au));
                    assert(pre.journal.persistent->image.accessible_aus().contains(au));
                }
            }
        };
        assert(post.branch_owned_aus() <= pre.branch_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.branch_owned_aus().contains(au)
                implies pre.branch_owned_aus().contains(au) by {
                if new_branch.ephemeral->v.full_accessible_aus().contains(au) {
                    let image = pre.branch.persistent->image;
                    assert((to_aus(image.persistent.dom())
                        + summary_aus(image.branch_summary())).contains(au));
                }
            }
        };
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(recover)]
    fn recover_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        records: MsgHistory,
        keys: Seq<Key>,
        msgs: Seq<Message>,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::ReadForRecovery{records};
        let branch_lbl = CrashAwareCachingDiskBranch::Label::Append{keys, msgs};
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskJournal::State::read_for_recovery(pre.journal, new_journal, journal_lbl)) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::read_for_recovery() => {},
                _ => { assert(false); },
            }
        }
        assert(CrashAwareCachingDiskBranch::State::append(
            pre.branch,
            new_branch,
            branch_lbl,
            new_branch.ephemeral->v,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.branch.ephemeral is Known {
            let old_b = pre.branch.ephemeral->v;
            let new_b = new_branch.ephemeral->v;
            let cb_lbl = CachingDiskBranch::Label::AppendLabel{keys, msgs};
            assert(CachingDiskBranch::State::next(old_b, new_b, cb_lbl));
            CachingDiskBranch::State::append_preserves_accessible_aus(old_b, new_b, cb_lbl);
            old_b.metadata_loaded_full_accessible_eq();
            new_b.metadata_loaded_full_accessible_eq();
            assert(new_b.full_accessible_aus() <= old_b.full_accessible_aus());
        }
        assert(post.free_aus == pre.free_aus);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        Self::branch_owned_aus_ephemeral_subset(pre.branch, post.branch);
        assert(post.branch_owned_aus() <= pre.branch_owned_aus());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        superblock_image: AbstractSuperblockImage,
    ) {
        let new_boundary_lsn = superblock_image.branch_seq_end;
        let journal_lbl = CrashAwareCachingDiskJournal::Label::CommitStart{
            new_boundary_lsn,
            snapshot: superblock_image.journal_snapshot,
            seq_end: superblock_image.journal_seq_end,
        };
        let branch_lbl = CrashAwareCachingDiskBranch::Label::CommitStart{
            new_boundary_lsn,
            sealed_roots: superblock_image.branch_roots,
        };
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskJournal::State::commit_start(
            pre.journal,
            new_journal,
            journal_lbl,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::commit_start() => {},
                _ => { assert(false); },
            }
        }
        assert(CrashAwareCachingDiskBranch::State::commit_start(
            pre.branch,
            new_branch,
            branch_lbl,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::commit_start() => {},
                _ => { assert(false); },
            }
        }
        assert(post.branch_owned_aus() <= pre.branch_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.branch_owned_aus().contains(au)
                implies pre.branch_owned_aus().contains(au) by {
                if new_branch.ephemeral->v.full_accessible_aus().contains(au) {
                    assert(new_branch.ephemeral == pre.branch.ephemeral);
                }
            }
        };
        assert(post.free_aus == pre.free_aus);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        assert(pre.journal.frozen is None) by {
            reveal(CrashAwareCachingDiskJournal::State::commit_start);
        }
        assert(pre.branch.frozen is None) by {
            reveal(CrashAwareCachingDiskBranch::State::commit_start);
        }
        assert(!pre.commit_started());
        assert(pre.superblockstore.in_flight is None) by {
            if pre.superblockstore.in_flight is Some {
                assert(pre.superblock_commit_wf());
                assert(pre.commit_started());
            }
        }
        assert(!pre.superblockstore.landed) by {
            if pre.superblockstore.landed {
                assert(pre.superblock_commit_wf());
                assert(pre.commit_started());
            }
        }
        assert(post.superblockstore == pre.superblockstore);
        assert(post.commit_started());
        assert(post.superblock_commit_wf());
        Self::allocation_wf_from_subset(pre, post);
    }

    #[inductive(commit_prepared)]
    fn commit_prepared_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        new_superblock: SuperblockStore::State,
        raw_page: RawPage,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::CommitPrepared;
        let branch_lbl = CrashAwareCachingDiskBranch::Label::FreezePrepared;
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        SuperblockStore::State::inv_next(pre.superblockstore, new_superblock, SuperblockStore::Label::Write{raw: raw_page});
        assert(CrashAwareCachingDiskJournal::State::commit_prepared(
            pre.journal,
            new_journal,
            journal_lbl,
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::commit_prepared() => {},
                _ => { assert(false); },
            }
        }
        reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        assert(new_journal.persistent == pre.journal.persistent);
        assert(new_journal.ephemeral == pre.journal.ephemeral);
        assert(new_journal.frozen == pre.journal.frozen);
        assert(new_journal.prepared);
        assert(CrashAwareCachingDiskBranch::State::freeze_prepared(pre.branch, new_branch, branch_lbl)) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::freeze_prepared() => {},
                _ => { assert(false); },
            }
        }
        reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
        assert(new_branch.persistent == pre.branch.persistent);
        assert(new_branch.ephemeral == pre.branch.ephemeral);
        assert(new_branch.frozen == pre.branch.frozen);
        assert(new_branch.prepared);
        let inner_branch_lbl = CachingDiskBranch::Label::FreezePrepared{image: pre.branch.frozen.unwrap()};
        assert(CachingDiskBranch::State::next(
            pre.branch.ephemeral->v,
            pre.branch.ephemeral->v,
            inner_branch_lbl,
        ));
        assert(CachingDiskBranch::State::freeze_prepared(
            pre.branch.ephemeral->v,
            pre.branch.ephemeral->v,
            inner_branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::next);
            reveal(CachingDiskBranch::State::next_by);
            let step = choose |step: CachingDiskBranch::Step|
                CachingDiskBranch::State::next_by(
                    pre.branch.ephemeral->v,
                    pre.branch.ephemeral->v,
                    inner_branch_lbl,
                    step,
                );
            match step {
                CachingDiskBranch::Step::freeze_prepared() => {},
                _ => { assert(false); },
            }
        }
        reveal(CachingDiskBranch::State::freeze_prepared);
        assert(post.journal == new_journal);
        assert(post.branch == new_branch);
        assert(post.free_aus == pre.free_aus);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.journal_owned_aus().contains(au)
                implies pre.journal_owned_aus().contains(au) by {
                if post.journal.frozen is Some
                    && post.journal.frozen.unwrap().snapshot.freshest_rec() is Some {
                    assert(pre.journal.frozen == post.journal.frozen);
                } else if post.journal.ephemeral is Known {
                    assert(post.journal.ephemeral == pre.journal.ephemeral);
                }
            }
        };
        assert(post.branch_owned_aus() <= pre.branch_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.branch_owned_aus().contains(au)
                implies pre.branch_owned_aus().contains(au) by {
                if post.branch.ephemeral->v.full_accessible_aus().contains(au) {
                    assert(post.branch.ephemeral == pre.branch.ephemeral);
                }
            }
        };
        Self::allocation_wf_from_subset(pre, post);
        assert(post.commit_started());
        assert(post.superblock_commit_wf());
    }

    #[inductive(superblock_write_lands)]
    fn superblock_write_lands_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_superblock: SuperblockStore::State,
    ) {
        SuperblockStore::State::inv_next(pre.superblockstore, new_superblock, SuperblockStore::Label::Land);
        assert(pre.superblockstore.in_flight is Some) by {
            reveal(SuperblockStore::State::next);
            reveal(SuperblockStore::State::next_by);
            assert(SuperblockStore::State::next_by(
                pre.superblockstore,
                new_superblock,
                SuperblockStore::Label::Land,
                SuperblockStore::Step::land(),
            ));
            reveal(SuperblockStore::State::land);
        }
        assert(pre.commit_started()) by {
            assert(pre.superblock_commit_wf());
        }
        assert(post.commit_started() == pre.commit_started());
        assert(post.superblock_commit_wf());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        new_superblock: SuperblockStore::State,
        discarded: Set<AU>,
    ) {
        let journal_lbl = CrashAwareCachingDiskJournal::Label::CommitComplete{
            require_end: pre.branch_lsn(),
            discarded,
        };
        let branch_lbl = CrashAwareCachingDiskBranch::Label::CommitComplete;
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        SuperblockStore::State::inv_next(pre.superblockstore, new_superblock, SuperblockStore::Label::Complete);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskJournal::State::next(pre.journal, new_journal, journal_lbl)) by {}
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step: CrashAwareCachingDiskJournal::Step|
            CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
        match journal_step {
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::commit_complete(
                    pre.journal,
                    new_journal,
                    journal_lbl,
                    new_ephemeral,
                ));
            },
            _ => { assert(false); },
        }
        assert(CrashAwareCachingDiskJournal::State::next(pre.journal, new_journal, journal_lbl)) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {},
                _ => { assert(false); },
            }
        }
        if pre.journal.ephemeral is Known {
            let old_e = pre.journal.ephemeral->v;
            let new_e = new_journal.ephemeral->v;
            let frozen = pre.journal.frozen.unwrap();
            let cj_lbl = CachingDiskJournal::Label::DiscardOld{
                start_lsn: frozen.snapshot.boundary_lsn,
                require_end: pre.branch_lsn(),
                deallocs: discarded,
            };
            assert(CachingDiskJournal::State::next(old_e, new_e, cj_lbl));
            CachingDiskJournal::State::discard_old_accessible_aus(
                old_e,
                new_e,
                frozen.snapshot.boundary_lsn,
                pre.branch_lsn(),
                discarded,
            );
        }
        assert(CrashAwareCachingDiskBranch::State::commit_complete(
            pre.branch,
            new_branch,
            branch_lbl,
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::commit_complete() => {},
                _ => { assert(false); },
            }
        }
        assert(post.journal == new_journal);
        assert(post.branch == new_branch);
        assert(post.free_aus <= pre.free_aus + discarded);
        assert(post.journal_owned_aus() <= pre.journal_owned_aus());
        assert(post.branch_owned_aus() <= pre.branch_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.branch_owned_aus().contains(au)
                implies pre.branch_owned_aus().contains(au) by {
                if post.branch.ephemeral->v.full_accessible_aus().contains(au) {
                    assert(post.branch.ephemeral == pre.branch.ephemeral);
                }
            }
        };
        assert(discarded <= pre.journal_owned_aus());
        assert(discarded.disjoint(post.journal_owned_aus())) by {
            assert(post.journal.frozen is None);
            assert(post.journal.ephemeral is Known);
            let new_e = post.journal.ephemeral->v;
            assert(discarded.disjoint(caching_disk_journal_accessible_aus(new_e)));
            assert forall |au: AU| #[trigger] discarded.contains(au)
                implies !post.journal_owned_aus().contains(au) by {
                if post.journal_owned_aus().contains(au) {
                    assert(caching_disk_journal_accessible_aus(new_e).contains(au));
                    assert(false);
                }
            }
        };
        assert(discarded.disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] discarded.contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                    assert(pre.branch_owned_aus().contains(au));
                }
            }
        };
        assert(discarded.disjoint(Self::reserved_aus())) by {
            assert forall |au: AU| #[trigger] discarded.contains(au)
                implies !Self::reserved_aus().contains(au) by {
                if Self::reserved_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                    assert(pre.component_owned_aus().contains(au));
                }
            }
        };
        assert(discarded.disjoint(post.component_owned_aus()));
        Self::allocation_wf_from_alloc_update(
            pre,
            post,
            Set::empty(),
            Set::empty(),
            discarded,
        );
        assert(post.superblockstore.in_flight is None && !post.superblockstore.landed) by {
            reveal(SuperblockStore::State::next);
            reveal(SuperblockStore::State::next_by);
            assert(SuperblockStore::State::next_by(
                pre.superblockstore,
                new_superblock,
                SuperblockStore::Label::Complete,
                SuperblockStore::Step::complete(),
            ));
            reveal(SuperblockStore::State::complete);
        }
        assert(post.superblock_commit_wf());
    }

    #[inductive(crash)]
    fn crash_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CrashAwareCachingDiskJournal::State,
        new_branch: CrashAwareCachingDiskBranch::State,
        new_superblock: SuperblockStore::State,
        keep_in_flight: bool,
    ) {
        assert(keep_in_flight == pre.superblockstore.landed);
        let journal_lbl = CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight};
        let branch_lbl = CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight};
        CrashAwareCachingDiskJournal::State::inv_next(pre.journal, new_journal, journal_lbl);
        CrashAwareCachingDiskBranch::State::inv_next(pre.branch, new_branch, branch_lbl);
        SuperblockStore::State::inv_next(pre.superblockstore, new_superblock, SuperblockStore::Label::Crash);
        Self::journal_next_knownness(pre.journal, new_journal, journal_lbl);
        Self::branch_next_knownness(pre.branch, new_branch, branch_lbl);
        assert(CrashAwareCachingDiskJournal::State::next(pre.journal, new_journal, journal_lbl)) by {}
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let journal_step = choose |step: CrashAwareCachingDiskJournal::Step|
            CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
        match journal_step {
            CrashAwareCachingDiskJournal::Step::crash() => {
                assert(CrashAwareCachingDiskJournal::State::crash(
                    pre.journal,
                    new_journal,
                    journal_lbl,
                ));
            },
            _ => { assert(false); },
        }
        assert(CrashAwareCachingDiskBranch::State::next(pre.branch, new_branch, branch_lbl)) by {}
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let branch_step = choose |step: CrashAwareCachingDiskBranch::Step|
            CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
        match branch_step {
            CrashAwareCachingDiskBranch::Step::crash() => {
                assert(CrashAwareCachingDiskBranch::State::crash(
                    pre.branch,
                    new_branch,
                    branch_lbl,
                ));
            },
            _ => { assert(false); },
        }
        assert(CrashAwareCachingDiskJournal::State::next(pre.journal, new_journal, journal_lbl)) by {
            reveal(CrashAwareCachingDiskJournal::State::next);
            reveal(CrashAwareCachingDiskJournal::State::next_by);
            let step = choose |step: CrashAwareCachingDiskJournal::Step|
                CrashAwareCachingDiskJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
            match step {
                CrashAwareCachingDiskJournal::Step::crash() => {},
                _ => { assert(false); },
            }
        }
        assert(CrashAwareCachingDiskBranch::State::next(pre.branch, new_branch, branch_lbl)) by {
            reveal(CrashAwareCachingDiskBranch::State::next);
            reveal(CrashAwareCachingDiskBranch::State::next_by);
            let step = choose |step: CrashAwareCachingDiskBranch::Step|
                CrashAwareCachingDiskBranch::State::next_by(pre.branch, new_branch, branch_lbl, step);
            match step {
                CrashAwareCachingDiskBranch::Step::crash() => {},
                _ => { assert(false); },
            }
        };
        assert(post.free_aus <= pre.free_aus);
        CrashAwareCachingDiskJournal::State::crash_persistent_image_accessible_aus(
            pre.journal,
            new_journal,
            journal_lbl,
        );
        let prepared_branch_image = if keep_in_flight && pre.branch.ephemeral is Known {
            CachingDiskBranchImage::materialized_from_persistent(
                pre.branch.ephemeral->v,
                pre.branch.frozen.unwrap(),
            )
        } else if pre.branch.ephemeral is Unknown {
            pre.branch.persistent->image
        } else {
            CachingDiskBranchImage::materialized_from_persistent(
                pre.branch.ephemeral->v,
                pre.branch.persistent.metadata(),
            )
        };
        if keep_in_flight {
            pre.branch.prepared_materialized_image_matches_visible_prefix();
            assert(prepared_branch_image == pre.branch.prepared_materialized_image());
            assert(to_aus(prepared_branch_image.persistent.dom())
                <= pre.branch.ephemeral->v.full_accessible_aus()) by {
                assert(prepared_branch_image.persistent == pre.branch.ephemeral->v.disk.persistent);
                assert(pre.branch.ephemeral->v.disk.persistent.dom()
                    <= pre.branch.ephemeral->v.disk.visible().dom());
                to_aus_preserves_lte(
                    pre.branch.ephemeral->v.disk.persistent.dom(),
                    pre.branch.ephemeral->v.disk.visible().dom(),
                );
                assert(to_aus(pre.branch.ephemeral->v.disk.visible().dom())
                    <= pre.branch.ephemeral->v.full_accessible_aus());
            }
            assert(summary_aus(prepared_branch_image.branch_summary())
                <= pre.branch.ephemeral->v.full_accessible_aus()) by {
                assert(summary_aus(prepared_branch_image.branch_summary())
                    <= summary_aus(pre.branch.ephemeral->v.interpreted_branch_summary()));
            }
        } else if pre.branch.ephemeral is Known {
            let persistent_meta = pre.branch.persistent.metadata();
            let cb_lbl = CachingDiskBranch::Label::FreezePrepared{
                image: persistent_meta,
            };
            assert(CachingDiskBranch::State::next(
                pre.branch.ephemeral->v,
                pre.branch.ephemeral->v,
                cb_lbl,
            )) by {
                reveal(CachingDiskBranch::State::next);
                reveal(CachingDiskBranch::State::next_by);
                assert(CachingDiskBranch::State::freeze_prepared(
                    pre.branch.ephemeral->v,
                    pre.branch.ephemeral->v,
                    cb_lbl,
                )) by {
                    reveal(CachingDiskBranch::State::freeze_prepared);
                };
                assert(CachingDiskBranch::State::next_by(
                    pre.branch.ephemeral->v,
                    pre.branch.ephemeral->v,
                    cb_lbl,
                    CachingDiskBranch::Step::freeze_prepared(),
                ));
            };
            pre.branch.ephemeral->v.prepared_image_matches_visible_prefix(prepared_branch_image);
            assert(to_aus(prepared_branch_image.persistent.dom())
                <= pre.branch.ephemeral->v.full_accessible_aus()) by {
                assert(prepared_branch_image.persistent == pre.branch.ephemeral->v.disk.persistent);
                assert(pre.branch.ephemeral->v.disk.persistent.dom()
                    <= pre.branch.ephemeral->v.disk.visible().dom());
                to_aus_preserves_lte(
                    pre.branch.ephemeral->v.disk.persistent.dom(),
                    pre.branch.ephemeral->v.disk.visible().dom(),
                );
                assert(to_aus(pre.branch.ephemeral->v.disk.visible().dom())
                    <= pre.branch.ephemeral->v.full_accessible_aus());
            }
            assert(summary_aus(prepared_branch_image.branch_summary())
                <= pre.branch.ephemeral->v.full_accessible_aus()) by {
                assert(summary_aus(prepared_branch_image.branch_summary())
                    <= summary_aus(pre.branch.ephemeral->v.interpreted_branch_summary()));
            }
        }
        assert(post.journal_owned_aus() <= pre.journal_owned_aus()) by {
            assert(post.journal == new_journal);
            assert(post.journal.ephemeral is Unknown);
            assert(post.journal.persistent is Image);
            assert forall |au: AU| #[trigger] post.journal_owned_aus().contains(au)
                implies pre.journal_owned_aus().contains(au) by {
                if pre.journal.ephemeral is Known {
                    assert(post.journal.persistent->image.accessible_aus()
                        <= caching_disk_journal_accessible_aus(pre.journal.ephemeral->v));
                    assert(caching_disk_journal_accessible_aus(pre.journal.ephemeral->v).contains(au));
                } else {
                    assert(post.journal.persistent == pre.journal.persistent);
                }
            }
        };
        assert(post.branch_owned_aus() <= pre.branch_owned_aus()) by {
            assert forall |au: AU| #[trigger] post.branch_owned_aus().contains(au)
                implies pre.branch_owned_aus().contains(au) by {
                if keep_in_flight {
                    assert(post.branch.persistent == PersistentCachingDiskBranch::Image{
                        image: prepared_branch_image,
                    });
                    if to_aus(post.branch.persistent->image.persistent.dom()).contains(au) {
                        assert(pre.branch.ephemeral->v.full_accessible_aus().contains(au));
                    } else if summary_aus(post.branch.persistent->image.branch_summary()).contains(au) {
                        assert(pre.branch.ephemeral->v.full_accessible_aus().contains(au));
                    }
                } else {
                    assert(post.branch.persistent == PersistentCachingDiskBranch::Image{
                        image: prepared_branch_image,
                    });
                    if pre.branch.ephemeral is Known {
                        if to_aus(post.branch.persistent->image.persistent.dom()).contains(au) {
                            assert(pre.branch.ephemeral->v.full_accessible_aus().contains(au));
                        } else if summary_aus(post.branch.persistent->image.branch_summary()).contains(au) {
                            assert(pre.branch.ephemeral->v.full_accessible_aus().contains(au));
                        }
                    } else {
                        assert(post.branch.persistent == pre.branch.persistent);
                    }
                }
            }
        };
        Self::allocation_wf_from_subset(pre, post);
        assert(post.superblockstore.in_flight is None && !post.superblockstore.landed) by {
            reveal(SuperblockStore::State::next);
            reveal(SuperblockStore::State::next_by);
            assert(SuperblockStore::State::next_by(
                pre.superblockstore,
                new_superblock,
                SuperblockStore::Label::Crash,
                SuperblockStore::Step::crash(),
            ));
            reveal(SuperblockStore::State::crash);
        }
        assert(post.superblock_commit_wf());
    }

    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, lbl: Label) {}

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            Self::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CrashAwareCachingDiskSystem::State::next);
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        let step = choose |step: CrashAwareCachingDiskSystem::Step|
            Self::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskSystem::Step::accept_request() => {
                Self::accept_request_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskSystem::Step::deliver_reply() => {
                Self::deliver_reply_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskSystem::Step::query(new_branch) => {
                Self::query_inductive(pre, post, lbl, new_branch);
            },
            CrashAwareCachingDiskSystem::Step::put(new_journal, new_branch) => {
                Self::put_inductive(pre, post, lbl, new_journal, new_branch);
            },
            CrashAwareCachingDiskSystem::Step::execute_noop() => {
                Self::execute_noop_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskSystem::Step::req_sync() => {
                Self::req_sync_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskSystem::Step::reply_sync() => {
                Self::reply_sync_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskSystem::Step::journal_internal(new_journal) => {
                Self::journal_internal_inductive(pre, post, lbl, new_journal);
            },
            CrashAwareCachingDiskSystem::Step::journal_observe_clean_aus(
                new_journal,
                aus,
            ) => {
                Self::journal_observe_clean_aus_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    aus,
                );
            },
            CrashAwareCachingDiskSystem::Step::journal_load_index(
                new_journal,
                discovered_aus,
            ) => {
                Self::journal_load_index_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    discovered_aus,
                );
            },
            CrashAwareCachingDiskSystem::Step::journal_internal_alloc(
                new_journal,
                allocs,
                deallocs,
                prune_aus,
            ) => {
                Self::journal_internal_alloc_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    allocs,
                    deallocs,
                    prune_aus,
                );
            },
            CrashAwareCachingDiskSystem::Step::map_internal(new_branch) => {
                Self::map_internal_inductive(pre, post, lbl, new_branch);
            },
            CrashAwareCachingDiskSystem::Step::component_internals(
                new_journal,
                new_branch,
            ) => {
                Self::component_internals_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                );
            },
            CrashAwareCachingDiskSystem::Step::map_load_metadata(
                new_branch,
                root,
                discovered_aus,
            ) => {
                Self::map_load_metadata_inductive(
                    pre,
                    post,
                    lbl,
                    new_branch,
                    root,
                    discovered_aus,
                );
            },
            CrashAwareCachingDiskSystem::Step::map_internal_alloc(
                new_branch,
                allocs,
                deallocs,
            ) => {
                Self::map_internal_alloc_inductive(
                    pre,
                    post,
                    lbl,
                    new_branch,
                    allocs,
                    deallocs,
                );
            },
            CrashAwareCachingDiskSystem::Step::load_ephemeral_from_persistent(
                new_journal,
                new_branch,
            ) => {
                Self::load_ephemeral_from_persistent_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                );
            },
            CrashAwareCachingDiskSystem::Step::recover(
                new_journal,
                new_branch,
                records,
                keys,
                msgs,
            ) => {
                Self::recover_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                    records,
                    keys,
                    msgs,
                );
            },
            CrashAwareCachingDiskSystem::Step::commit_start(
                new_journal,
                new_branch,
                superblock_image,
            ) => {
                Self::commit_start_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                    superblock_image,
                );
            },
            CrashAwareCachingDiskSystem::Step::commit_prepared(
                new_journal,
                new_branch,
                new_superblock,
                raw_page,
            ) => {
                Self::commit_prepared_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                    new_superblock,
                    raw_page,
                );
            },
            CrashAwareCachingDiskSystem::Step::superblock_write_lands(
                new_superblock,
            ) => {
                Self::superblock_write_lands_inductive(
                    pre,
                    post,
                    lbl,
                    new_superblock,
                );
            },
            CrashAwareCachingDiskSystem::Step::commit_complete(
                new_journal,
                new_branch,
                new_superblock,
                discarded,
            ) => {
                Self::commit_complete_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                    new_superblock,
                    discarded,
                );
            },
            CrashAwareCachingDiskSystem::Step::crash(
                new_journal,
                new_branch,
                new_superblock,
                keep_in_flight,
            ) => {
                Self::crash_inductive(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    new_branch,
                    new_superblock,
                    keep_in_flight,
                );
            },
            CrashAwareCachingDiskSystem::Step::noop() => {
                Self::noop_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskSystem::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }
}}

impl CrashAwareCachingDiskSystem::State {
    pub proof fn allocation_wf_from_subset(pre: Self, post: Self)
        requires
            pre.allocation_wf(),
            post.free_aus <= pre.free_aus,
            post.journal_owned_aus() <= pre.journal_owned_aus(),
            post.branch_owned_aus() <= pre.branch_owned_aus(),
        ensures
            post.allocation_wf(),
    {
        assert forall |au: AU| #[trigger] post.free_aus.contains(au)
            implies !post.component_owned_aus().contains(au) by {
            assert(pre.free_aus.contains(au));
            if post.component_owned_aus().contains(au) {
                if Self::reserved_aus().contains(au) {
                    assert(pre.component_owned_aus().contains(au));
                } else if post.journal_owned_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                    assert(pre.component_owned_aus().contains(au));
                } else {
                    assert(post.branch_owned_aus().contains(au));
                    assert(pre.branch_owned_aus().contains(au));
                    assert(pre.component_owned_aus().contains(au));
                }
                assert(false);
            }
        }
        assert(Self::reserved_aus().disjoint(post.journal_owned_aus())) by {
            assert forall |au: AU| #[trigger] Self::reserved_aus().contains(au)
                implies !post.journal_owned_aus().contains(au) by {
                if post.journal_owned_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                }
            }
        };
        assert(Self::reserved_aus().disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] Self::reserved_aus().contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    assert(pre.branch_owned_aus().contains(au));
                }
            }
        };
        assert(post.journal_owned_aus().disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] post.journal_owned_aus().contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    assert(pre.journal_owned_aus().contains(au));
                    assert(pre.branch_owned_aus().contains(au));
                }
            }
        };
    }

    pub proof fn allocation_wf_from_growth(
        pre: Self,
        post: Self,
        journal_growth: Set<AU>,
        branch_growth: Set<AU>,
    )
        requires
            pre.allocation_wf(),
            journal_growth <= pre.free_aus,
            branch_growth <= pre.free_aus,
            journal_growth.disjoint(branch_growth),
            post.free_aus <= pre.free_aus - (journal_growth + branch_growth),
            post.journal_owned_aus() <= pre.journal_owned_aus() + journal_growth,
            post.branch_owned_aus() <= pre.branch_owned_aus() + branch_growth,
        ensures
            post.allocation_wf(),
    {
        assert forall |au: AU| #[trigger] post.free_aus.contains(au)
            implies !post.component_owned_aus().contains(au) by {
            assert(pre.free_aus.contains(au));
            assert(!journal_growth.contains(au));
            assert(!branch_growth.contains(au));
            if post.component_owned_aus().contains(au) {
                if Self::reserved_aus().contains(au) {
                    assert(pre.component_owned_aus().contains(au));
                } else if post.journal_owned_aus().contains(au) {
                    if pre.journal_owned_aus().contains(au) {
                        assert(pre.component_owned_aus().contains(au));
                    } else {
                        assert(journal_growth.contains(au));
                    }
                } else {
                    assert(post.branch_owned_aus().contains(au));
                    if pre.branch_owned_aus().contains(au) {
                        assert(pre.component_owned_aus().contains(au));
                    } else {
                        assert(branch_growth.contains(au));
                    }
                }
                assert(false);
            }
        }
        assert(Self::reserved_aus().disjoint(post.journal_owned_aus())) by {
            assert forall |au: AU| #[trigger] Self::reserved_aus().contains(au)
                implies !post.journal_owned_aus().contains(au) by {
                if post.journal_owned_aus().contains(au) {
                    if pre.journal_owned_aus().contains(au) {
                    } else {
                        assert(journal_growth.contains(au));
                        assert(pre.free_aus.contains(au));
                        assert(pre.component_owned_aus().contains(au));
                    }
                }
            }
        };
        assert(Self::reserved_aus().disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] Self::reserved_aus().contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    if pre.branch_owned_aus().contains(au) {
                    } else {
                        assert(branch_growth.contains(au));
                        assert(pre.free_aus.contains(au));
                        assert(pre.component_owned_aus().contains(au));
                    }
                }
            }
        };
        assert(post.journal_owned_aus().disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] post.journal_owned_aus().contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    if pre.journal_owned_aus().contains(au) {
                        if pre.branch_owned_aus().contains(au) {
                            assert(false);
                        } else {
                            assert(branch_growth.contains(au));
                            assert(pre.free_aus.contains(au));
                            assert(pre.component_owned_aus().contains(au));
                        }
                    } else {
                        assert(journal_growth.contains(au));
                        if pre.branch_owned_aus().contains(au) {
                            assert(pre.free_aus.contains(au));
                            assert(pre.component_owned_aus().contains(au));
                        } else {
                            assert(branch_growth.contains(au));
                        }
                    }
                }
            }
        };
    }

    pub proof fn allocation_wf_from_alloc_update(
        pre: Self,
        post: Self,
        journal_growth: Set<AU>,
        branch_growth: Set<AU>,
        returned: Set<AU>,
    )
        requires
            pre.allocation_wf(),
            journal_growth <= pre.free_aus,
            branch_growth <= pre.free_aus,
            journal_growth.disjoint(branch_growth),
            post.free_aus <= (pre.free_aus - (journal_growth + branch_growth)) + returned,
            post.journal_owned_aus() <= pre.journal_owned_aus() + journal_growth,
            post.branch_owned_aus() <= pre.branch_owned_aus() + branch_growth,
            returned.disjoint(post.component_owned_aus()),
        ensures
            post.allocation_wf(),
    {
        assert forall |au: AU| #[trigger] post.free_aus.contains(au)
            implies !post.component_owned_aus().contains(au) by {
            if returned.contains(au) {
            } else {
                assert(pre.free_aus.contains(au));
                assert(!journal_growth.contains(au));
                assert(!branch_growth.contains(au));
                if post.component_owned_aus().contains(au) {
                    if Self::reserved_aus().contains(au) {
                        assert(pre.component_owned_aus().contains(au));
                    } else if post.journal_owned_aus().contains(au) {
                        if pre.journal_owned_aus().contains(au) {
                            assert(pre.component_owned_aus().contains(au));
                        } else {
                            assert(journal_growth.contains(au));
                        }
                    } else {
                        assert(post.branch_owned_aus().contains(au));
                        if pre.branch_owned_aus().contains(au) {
                            assert(pre.component_owned_aus().contains(au));
                        } else {
                            assert(branch_growth.contains(au));
                        }
                    }
                    assert(false);
                }
            }
        }
        Self::allocation_wf_from_growth_like_components(pre, post, journal_growth, branch_growth);
    }

    proof fn allocation_wf_from_growth_like_components(
        pre: Self,
        post: Self,
        journal_growth: Set<AU>,
        branch_growth: Set<AU>,
    )
        requires
            pre.allocation_wf(),
            journal_growth <= pre.free_aus,
            branch_growth <= pre.free_aus,
            journal_growth.disjoint(branch_growth),
            post.journal_owned_aus() <= pre.journal_owned_aus() + journal_growth,
            post.branch_owned_aus() <= pre.branch_owned_aus() + branch_growth,
        ensures
            post.component_disjoint(),
    {
        assert(Self::reserved_aus().disjoint(post.journal_owned_aus())) by {
            assert forall |au: AU| #[trigger] Self::reserved_aus().contains(au)
                implies !post.journal_owned_aus().contains(au) by {
                if post.journal_owned_aus().contains(au) {
                    if pre.journal_owned_aus().contains(au) {
                    } else {
                        assert(journal_growth.contains(au));
                        assert(pre.free_aus.contains(au));
                        assert(pre.component_owned_aus().contains(au));
                    }
                }
            }
        };
        assert(Self::reserved_aus().disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] Self::reserved_aus().contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    if pre.branch_owned_aus().contains(au) {
                    } else {
                        assert(branch_growth.contains(au));
                        assert(pre.free_aus.contains(au));
                        assert(pre.component_owned_aus().contains(au));
                    }
                }
            }
        };
        assert(post.journal_owned_aus().disjoint(post.branch_owned_aus())) by {
            assert forall |au: AU| #[trigger] post.journal_owned_aus().contains(au)
                implies !post.branch_owned_aus().contains(au) by {
                if post.branch_owned_aus().contains(au) {
                    if pre.journal_owned_aus().contains(au) {
                        if pre.branch_owned_aus().contains(au) {
                            assert(false);
                        } else {
                            assert(branch_growth.contains(au));
                            assert(pre.free_aus.contains(au));
                            assert(pre.component_owned_aus().contains(au));
                        }
                    } else {
                        assert(journal_growth.contains(au));
                        if pre.branch_owned_aus().contains(au) {
                            assert(pre.free_aus.contains(au));
                            assert(pre.component_owned_aus().contains(au));
                        } else {
                            assert(branch_growth.contains(au));
                        }
                    }
                }
            }
        };
    }

    proof fn journal_next_knownness(
        pre: CrashAwareCachingDiskJournal::State,
        post: CrashAwareCachingDiskJournal::State,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
        ensures
            match lbl {
                CrashAwareCachingDiskJournal::Label::LoadEphemeral => post.ephemeral is Known,
                CrashAwareCachingDiskJournal::Label::Crash{..} => post.ephemeral is Unknown,
                _ => (post.ephemeral is Known) == (pre.ephemeral is Known),
            },
    {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let step = choose |step| CrashAwareCachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
                assert(CrashAwareCachingDiskJournal::State::load_ephemeral(pre, post, lbl));
            },
            CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
                assert(CrashAwareCachingDiskJournal::State::read_for_recovery(pre, post, lbl));
            },
            CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
                assert(CrashAwareCachingDiskJournal::State::query_end_lsn(pre, post, lbl));
            },
            CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::put(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::load_index(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::observe_clean_aus(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::internal(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::internal_alloc(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskJournal::Step::query_lsn_persistence() => {
                assert(CrashAwareCachingDiskJournal::State::query_lsn_persistence(pre, post, lbl));
            },
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                assert(CrashAwareCachingDiskJournal::State::commit_start(pre, post, lbl));
            },
            CrashAwareCachingDiskJournal::Step::commit_prepared() => {
                assert(CrashAwareCachingDiskJournal::State::commit_prepared(pre, post, lbl));
            },
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::commit_complete(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskJournal::Step::crash() => {
                assert(CrashAwareCachingDiskJournal::State::crash(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }

    proof fn branch_next_knownness(
        pre: CrashAwareCachingDiskBranch::State,
        post: CrashAwareCachingDiskBranch::State,
        lbl: CrashAwareCachingDiskBranch::Label,
    )
        requires
            CrashAwareCachingDiskBranch::State::next(pre, post, lbl),
        ensures
            match lbl {
                CrashAwareCachingDiskBranch::Label::LoadEphemeral => post.ephemeral is Known,
                CrashAwareCachingDiskBranch::Label::Crash{..} => post.ephemeral is Unknown,
                _ => (post.ephemeral is Known) == (pre.ephemeral is Known),
            },
    {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_ephemeral(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskBranch::Step::query(msg) => {
                assert(CrashAwareCachingDiskBranch::State::query(pre, post, lbl, msg));
            },
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::append(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::internal(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::internal_alloc(pre, post, lbl, new_ephemeral));
            },
            CrashAwareCachingDiskBranch::Step::commit_start() => {
                assert(CrashAwareCachingDiskBranch::State::commit_start(pre, post, lbl));
            },
            CrashAwareCachingDiskBranch::Step::freeze_prepared() => {
                assert(CrashAwareCachingDiskBranch::State::freeze_prepared(pre, post, lbl));
            },
            CrashAwareCachingDiskBranch::Step::commit_complete() => {
                assert(CrashAwareCachingDiskBranch::State::commit_complete(pre, post, lbl));
            },
            CrashAwareCachingDiskBranch::Step::crash() => {
                assert(CrashAwareCachingDiskBranch::State::crash(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub open spec fn empty_superblock_page() -> RawPage
    {
        crate::implementation::AbstractSuperblock_v::marshal_abstract_superblock(
            empty_abstract_superblock_image(),
        )
    }

    pub open spec fn empty_journal() -> CrashAwareCachingDiskJournal::State
    {
        CrashAwareCachingDiskJournal::State{
            persistent: PersistentCachingDiskJournal::Image{
                image: CachingDiskJournalImage::empty(),
            },
            ephemeral: EphemeralCachingDiskJournal::Unknown,
            frozen: None,
            prepared: false,
        }
    }

    pub open spec fn empty_branch() -> CrashAwareCachingDiskBranch::State
    {
        CrashAwareCachingDiskBranch::State{
            persistent: PersistentCachingDiskBranch::Image{
                image: empty_caching_disk_branch_image(),
            },
            ephemeral: EphemeralCachingDiskBranch::Unknown,
            frozen: None,
            prepared: false,
        }
    }

    pub open spec fn reserved_aus() -> Set<AU>
    {
        set![spec_superblock_addr().au]
    }

    pub open spec fn superblock_inflight(self) -> bool
    {
        self.commit_started() && !self.superblockstore.landed
    }

    pub open spec fn superblock_landed(self) -> bool
    {
        self.commit_started() && self.superblockstore.landed
    }

    pub open spec fn coordination_i(self) -> CoordinationSystem::State
    {
        CoordinationSystem::State{
            journal: self.journal.i_abstract(),
            mapadt: self.branch.i().abstract_i(),
            progress: self.progress,
            sync_reqs: self.sync_reqs,
            superblock_in_flight: self.superblock_inflight(),
            superblock_landed: self.superblock_landed(),
        }
    }

    pub open spec fn branch_lsn(self) -> LSN
    {
        if self.branch.ephemeral is Known {
            self.branch.ephemeral->v.seq_end
        } else {
            self.branch.persistent.metadata().seq_end
        }
    }

}

}
