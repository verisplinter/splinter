// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// A staged replacement candidate for AtomicState_v.
//
// This model keeps journal and branch fields present from initialization, but
// service readiness is represented by their internal status fields.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::multiset::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, AUPageBounds, lsn_au_index_discard_up_to,
};
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AllocationBranchStackRefinement_v::append_puts;
use crate::implementation::Cache_v::{addr_maps_to_req, Cache, Entry, Slot, Status};
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedBranch, LoadedPathReceipt,
    root_summary_from_read, root_summary_read_valid,
};
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot};
use crate::implementation::CachingDiskBranch_v::{sealed_summary_aus_between, split_read_addrs};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, empty_abstract_superblock_image, marshal_abstract_superblock,
    superblock_matches,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::journal::LinkedJournal_v::JournalRecord;
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{ID, Input, MapSpec, Reply, Request, SyncReqId};
use crate::spec::Messages_t::{Message, Value, nop_delta};

verus! {

pub open spec fn au_page_bounds_from_reads_page_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
) -> AUPageBounds
    decreases depth
{
    if root is None || depth == 0 {
        Map::empty()
    } else {
        let addr = root.unwrap();
        let prior = au_page_bounds_from_reads_page_walk_depth(
            reads,
            boundary_lsn,
            reads[addr].cropped_prior(boundary_lsn),
            (depth - 1) as nat,
        );
        let page = if prior.contains_key(addr.au) {
            if addr.page <= prior[addr.au] {
                prior[addr.au]
            } else {
                addr.page
            }
        } else {
            addr.page
        };
        prior.insert(addr.au, page)
    }
}

pub open spec fn au_page_bounds_from_reads_au_walk_depth(
    reads: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    first: AU,
    au_depth: nat,
    page_depth: nat,
) -> AUPageBounds
    decreases au_depth
{
    if root is None || au_depth == 0 {
        Map::empty()
    } else {
        let addr = root.unwrap();
        if addr.au == first {
            au_page_bounds_from_reads_page_walk_depth(
                reads,
                boundary_lsn,
                root,
                page_depth,
            )
        } else {
            let bottom = addr.first_page();
            let prior = au_page_bounds_from_reads_au_walk_depth(
                reads,
                boundary_lsn,
                reads[bottom].cropped_prior(boundary_lsn),
                first,
                (au_depth - 1) as nat,
                page_depth,
            );
            let page = if prior.contains_key(addr.au) {
                if addr.page <= prior[addr.au] {
                    prior[addr.au]
                } else {
                    addr.page
                }
            } else {
                addr.page
            };
            prior.insert(addr.au, page)
        }
    }
}

#[verifier::ext_equal]
pub struct AtomicJournalImage {
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

impl AtomicJournalImage {
    pub open spec fn wf(self) -> bool
    {
        self.snapshot.boundary_lsn <= self.seq_end
    }
}

state_machine!{ AtomicJournalState {
    fields {
        pub journal: CachedJournal::State,
        pub mini_allocator: MiniAllocator,
        pub au_page_bounds: AUPageBounds,
        pub persistent_seq_end: LSN,
        pub in_flight: Option<AtomicJournalImage>,
        pub prepared: bool,
    }

    pub enum Label {
        Put{ messages: MsgHistory },
        LoadIndex{ reads: Map<Address, JournalRecord>, discovered_aus: Set<AU> },
        ReadForRecovery{ messages: MsgHistory, reads: Map<Address, JournalRecord> },
        JournalMarshal{ addr: Address, writes: Map<Address, JournalRecord> },
        ObserveCleanAUs{ aus: Set<AU> },
        FillAUs{ aus: Set<AU> },
        QueryEndLsn{ end_lsn: LSN },
        CommitStart{
            snapshot: JournalSnapshot,
            seq_end: LSN,
            reads: Map<Address, JournalRecord>,
        },
        CommitPrepared,
        CommitComplete{
            require_end: LSN,
            discarded_aus: Set<AU>,
        },
    }

    init!{ initialize(snapshot: JournalSnapshot, initial_persistent_seq_end: LSN) {
        init journal = CachedJournal::State{
            snapshot,
            status: None,
        };
        init mini_allocator = MiniAllocator::empty();
        init au_page_bounds = Map::empty();
        init persistent_seq_end = initial_persistent_seq_end;
        init in_flight = None;
        init prepared = false;
    }}

    transition!{ put(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::Put{messages} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::Put{messages},
        );

        update journal = new_journal;
    }}

    transition!{ load_index(
        lbl: Label,
        new_journal: CachedJournal::State,
        au_depth: nat,
        page_depth: nat,
    ) {
        require let Label::LoadIndex{reads, discovered_aus} = lbl;
        let ptr = pre.journal.snapshot.freshest_rec();
        let bdy = pre.journal.snapshot.boundary_lsn;
        let first = pre.journal.snapshot.first();
        let new_au_page_bounds = au_page_bounds_from_reads_au_walk_depth(
            reads,
            bdy,
            ptr,
            first,
            au_depth,
            page_depth,
        );
        require CachedJournal::State::load_index(
            pre.journal,
            new_journal,
            CachedJournal::Label::LoadIndex{reads, discovered_aus},
            au_depth,
            page_depth,
        );
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::LoadIndex{reads, discovered_aus},
        );

        update journal = new_journal;
        update au_page_bounds = new_au_page_bounds;
    }}

    transition!{ read_for_recovery(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::ReadForRecovery{messages, reads} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::ReadForRecovery{messages, reads},
        );

        update journal = new_journal;
    }}

    transition!{ journal_marshal(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::JournalMarshal{addr, writes} = lbl;
        require pre.mini_allocator.tight_next_addr(pre.journal.snapshot.freshest_rec(), addr);
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::JournalMarshal{writes},
        );

        update journal = new_journal;
        update mini_allocator = pre.mini_allocator.allocate(addr).observe(addr);
        update au_page_bounds = pre.au_page_bounds.insert(addr.au, addr.page);
    }}

    transition!{ observe_clean_aus(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::ObserveCleanAUs{aus} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::ObserveCleanAUs{aus},
        );

        update journal = new_journal;
    }}

    transition!{ fill_aus(lbl: Label) {
        require let Label::FillAUs{aus} = lbl;

        update mini_allocator = pre.mini_allocator.add_aus(aus);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::QueryEndLsn{end_lsn},
        );
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{snapshot, seq_end, reads} = lbl;
        require pre.in_flight is None;
        require pre.persistent_seq_end <= snapshot.boundary_lsn;
        require snapshot.boundary_lsn <= seq_end;
        require seq_end == journal_snapshot_seq_end_from_reads(snapshot, reads);
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::FreezeForCommit{frozen: snapshot, reads},
        );

        update in_flight = Option::Some(AtomicJournalImage{snapshot, seq_end});
        update prepared = false;
    }}

    transition!{ commit_prepared(lbl: Label) {
        require lbl is CommitPrepared;
        require pre.in_flight is Some;
        let image = pre.in_flight.unwrap();
        require pre.journal.status is Some;
        require image.snapshot.freshest_rec() is Some ==>
            image.seq_end <= pre.journal.clean_watermark();

        update prepared = true;
    }}

    transition!{ commit_complete(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::CommitComplete{
            require_end,
            discarded_aus,
        } = lbl;
        require pre.in_flight is Some;
        require pre.prepared;
        let image = pre.in_flight.unwrap();
        let old_au_index = pre.journal.status.unwrap().lsn_au_index;
        let new_au_index = lsn_au_index_discard_up_to(
            old_au_index,
            image.snapshot.boundary_lsn,
        );
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::DiscardOld{
                start_lsn: image.snapshot.boundary_lsn,
                require_end,
                deallocs: discarded_aus,
            },
        );

        update journal = new_journal;
        update persistent_seq_end = image.seq_end;
        update mini_allocator = pre.mini_allocator.prune(discarded_aus);
        update au_page_bounds = AllocationJournal::State::au_page_bounds_restrict(
            pre.au_page_bounds,
            new_au_index.values(),
        );
        update in_flight = Option::None;
        update prepared = false;
    }}
}}

#[verifier::ext_equal]
pub struct AtomicBranchImage {
    pub sealed_roots: Seq<Address>,
    pub seq_end: nat,
}

state_machine!{ AtomicBranchState {
    fields {
        pub image: AtomicBranchImage,
        pub persistent_image: AtomicBranchImage,
        pub in_flight: Option<AtomicBranchImage>,
        pub prepared: bool,
        pub branch_summary: Map<AU, Summary>,
        pub persisted_root_count: nat,
        pub active_branch: CachedBranch::State,
        pub mini_allocator: MiniAllocator,
        pub seq_end: nat,
    }

    pub enum Label {
        Query{
            key: Key,
            msg: Message,
            receipts: Seq<LoadedPathReceipt>,
            read_nodes: LoadedBranch,
        },
        LoadMetadata{ root: Address, discovered_aus: Set<AU>, read_nodes: LoadedBranch },
        Append{
            keys: Seq<Key>,
            msgs: Seq<Message>,
            receipt: LoadedPathReceipt,
            init_root: Option<Address>,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Grow{ new_root_addr: Address, read_nodes: LoadedBranch, write_nodes: LoadedBranch },
        Split{
            new_child_addr: Address,
            receipt: LoadedPathReceipt,
            split_arg: SplitArg,
            read_nodes: LoadedBranch,
            write_nodes: LoadedBranch,
        },
        Seal{ aux_ptr: Pointer, summary: Summary, read_nodes: LoadedBranch, write_nodes: LoadedBranch },
        FillAUs{ aus: Set<AU> },
        ObservePersistedRoots{ target_count: nat },
        CommitStart{ branch_image: AtomicBranchImage },
        CommitPrepared,
        CommitComplete,
    }

    init!{ initialize(branch_image: AtomicBranchImage, initial_persisted_root_count: nat) {
        init image = branch_image;
        init persistent_image = branch_image;
        init in_flight = None;
        init prepared = false;
        init branch_summary = Map::empty();
        init persisted_root_count = initial_persisted_root_count;
        init active_branch = CachedBranch::State::empty_active();
        init mini_allocator = MiniAllocator::empty();
        init seq_end = branch_image.seq_end;
    }}

    transition!{ query(lbl: Label) {
        require let Label::Query{key, msg, receipts, read_nodes} = lbl;
        let roots = query_roots(pre.image.sealed_roots, pre.active_branch);
        require query_receipts_valid(roots, receipts, read_nodes, key);
        require msg == query_from_receipts_up_to(receipts, receipts.len() as nat);
    }}

    transition!{ load_metadata(lbl: Label) {
        require let Label::LoadMetadata{root, discovered_aus, read_nodes} = lbl;
        require pre.image.sealed_roots.contains(root);
        require root_summary_read_valid(root, read_nodes);
        require discovered_aus == root_summary_from_read(root, read_nodes);

        update branch_summary = pre.branch_summary.insert(root.au, discovered_aus);
    }}

    transition!{ append_nonempty(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Append{keys, msgs, receipt, init_root, read_nodes, write_nodes} = lbl;
        require pre.active_branch.root is Some;
        require init_root is None;
        let branch_lbl = CachedBranch::Label::Append{
            mini_allocator: pre.mini_allocator,
            receipt,
            keys,
            msgs,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update seq_end = pre.seq_end + keys.len();
    }}

    transition!{ append_empty(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Append{keys, msgs, receipt, init_root, read_nodes, write_nodes} = lbl;
        require pre.active_branch.root is None;
        require init_root is Some;

        let branch_lbl = CachedBranch::Label::Initialize{
            mini_allocator: pre.mini_allocator,
            init_root: init_root.unwrap(),
            keys,
            msgs,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update mini_allocator = pre.mini_allocator.allocate(init_root.unwrap());
        update seq_end = pre.seq_end + keys.len();
    }}

    transition!{ grow(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Grow{new_root_addr, read_nodes, write_nodes} = lbl;
        let branch_lbl = CachedBranch::Label::Grow{
            mini_allocator: pre.mini_allocator,
            new_root_addr,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update mini_allocator = pre.mini_allocator.allocate(new_root_addr);
    }}

    transition!{ split(lbl: Label, new_active_branch: CachedBranch::State) {
        require let Label::Split{new_child_addr, receipt, split_arg, read_nodes, write_nodes} = lbl;
        let branch_lbl = CachedBranch::Label::Split{
            mini_allocator: pre.mini_allocator,
            new_child_addr,
            receipt,
            split_arg,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);

        update active_branch = new_active_branch;
        update mini_allocator = pre.mini_allocator.allocate(new_child_addr);
    }}

    transition!{ seal(lbl: Label) {
        require let Label::Seal{aux_ptr, summary, read_nodes, write_nodes} = lbl;
        let root = pre.active_branch.root.unwrap();
        let branch_lbl = CachedBranch::Label::Seal{
            mini_allocator: pre.mini_allocator,
            aux_ptr,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl);
        require summary == pre.mini_allocator.reserved_aus();

        update image = AtomicBranchImage{
            sealed_roots: pre.image.sealed_roots.push(root),
            seq_end: pre.image.seq_end,
        };
        update active_branch = CachedBranch::State::empty_active();
        update mini_allocator = pre.mini_allocator.prune(summary);
        update branch_summary = pre.branch_summary.insert(root.au, summary);
    }}

    transition!{ fill_aus(lbl: Label) {
        require let Label::FillAUs{aus} = lbl;

        update mini_allocator = pre.mini_allocator.add_aus(aus);
    }}

    transition!{ observe_persisted_roots(lbl: Label) {
        require let Label::ObservePersistedRoots{target_count} = lbl;
        require pre.persisted_root_count <= target_count <= pre.image.sealed_roots.len();

        update persisted_root_count = target_count;
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{branch_image} = lbl;
        require pre.in_flight is None;
        require {
            ||| {
                &&& pre.metadata_loaded()
                &&& pre.active_branch.root is None
                &&& branch_image == pre.freeze_image()
            }
            ||| branch_image == pre.persistent_image
        };

        update in_flight = Option::Some(branch_image);
        update prepared = false;
    }}

    transition!{ commit_prepared(lbl: Label) {
        require lbl is CommitPrepared;
        require pre.in_flight is Some;
        let image = pre.in_flight.unwrap();
        require image.sealed_roots.len() <= pre.persisted_root_count;
        require image.sealed_roots.len() <= pre.image.sealed_roots.len();
        require pre.image.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots;

        update prepared = true;
    }}

    transition!{ commit_complete(lbl: Label) {
        require lbl is CommitComplete;
        require pre.in_flight is Some;
        require pre.prepared;
        let image = pre.in_flight.unwrap();
        let committed_root_count = image.sealed_roots.len() as nat;
        let new_persisted_root_count = if pre.persisted_root_count < committed_root_count {
            committed_root_count
        } else {
            pre.persisted_root_count
        };

        update persisted_root_count = new_persisted_root_count;
        update persistent_image = image;
        update in_flight = Option::None;
        update prepared = false;
    }}
}}

#[verifier::ext_equal]
pub struct AtomicInflightInfo {
    pub req_id: ID,
    pub boundary_lsn: LSN,
}

#[verifier::ext_equal]
pub struct AnotherAtomicState {
    pub recovery_state: RecoveryState,
    pub cache: Cache::State,
    pub outstanding_cache_reqs: Map<ID, Address>,
    pub free_aus: Set<AU>,
    pub journal: AtomicJournalState::State,
    pub branch: AtomicBranchState::State,
    pub persistent_image: Option<AbstractSuperblockImage>,
    pub in_flight: Option<AtomicInflightInfo>,
    pub sync_req_map: Map<SyncReqId, LSN>,
}

pub enum DiskEvent {
    InitiateRecovery{req_id: ID},
    SuperblockRecovery{req_id: ID, raw_page: RawPage, image: AbstractSuperblockImage},
    ExecuteSyncBegin{
        req_id: ID,
        image: AbstractSuperblockImage,
        journal_reads: Map<Address, RawPage>,
    },
    ExecuteSyncPrepared{req: DiskRequest},
    ExecuteSyncEnd{journal_discarded_aus: Set<AU>},
    CacheIOBegin{req_map: Map<ID, DiskRequest>},
    CacheIOEnd{resp_map: Map<ID, DiskResponse>},
}

pub enum InternalEvent {
    CacheInternal{},
    JournalLoadIndex{
        cache_reads: Map<Address, RawPage>,
        journal_reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
    },
    ReadForRecovery{
        addr: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        journal_reads: Map<Address, RawPage>,
        branch_reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    },
    JournalMarshall{addr: Address, raw_page: RawPage},
    ObserveCleanJournalAUs{aus: Set<AU>},
    JournalFillAUs{aus: Set<AU>},
    BranchLoadMetadata{root: Address, reads: Map<Address, RawPage>, discovered_aus: Set<AU>},
    MetadataLoadComplete{},
    BranchGrow{new_root_addr: Address, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, branch: AtomicBranchState::State},
    BranchSplit{new_child_addr: Address, receipt: LoadedPathReceipt, split_arg: SplitArg, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, branch: AtomicBranchState::State},
    BranchSeal{aux_ptr: Pointer, summary: Summary, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, branch: AtomicBranchState::State},
    BranchFillAUs{aus: Set<AU>},
    ObservePersistedBranchRoots{target_count: nat, aus: Set<AU>},
    RecoveryComplete{},
    AcceptSyncRequest{sync_req_id: SyncReqId},
    DeliverSyncReply{sync_req_id: SyncReqId},
}

pub enum ProgramEvent {
    NoOp{},
    Put{
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    },
    Query{
        end_lsn: LSN,
        key: Key,
        value: Value,
        msg: Message,
        receipts: Seq<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    },
}

pub open spec fn empty_branch_image() -> AtomicBranchImage
{
    AtomicBranchImage{
        sealed_roots: Seq::empty(),
        seq_end: 0,
    }
}

pub open spec fn empty_commit_image() -> AbstractSuperblockImage
{
    empty_abstract_superblock_image()
}

pub open spec fn to_branch_nodes(reads: Map<Address, RawPage>) -> LoadedBranch
{
    Map::new(
        |addr| reads.contains_key(addr),
        |addr| raw_page_to_branch_node(reads[addr]),
    )
}

pub open spec fn mini_allocator_allocated_addrs(mini_allocator: MiniAllocator) -> Set<Address>
{
    Set::new(|addr: Address| {
        &&& mini_allocator.allocs.contains_key(addr.au)
        &&& (mini_allocator.allocs[addr.au].reserved
            + mini_allocator.allocs[addr.au].observed).contains(addr)
    })
}

pub open spec fn atomic_branch_support_addrs(branch: AtomicBranchState::State) -> Set<Address>
{
    addresses_in_aus(summary_aus(branch.branch_summary))
        + mini_allocator_allocated_addrs(branch.mini_allocator)
}

pub open spec fn journal_snapshot_seq_end_from_reads(
    snapshot: JournalSnapshot,
    reads: Map<Address, JournalRecord>,
) -> LSN
{
    if snapshot.freshest_rec() is Some {
        reads[snapshot.freshest_rec().unwrap()].message_seq.seq_end
    } else {
        snapshot.boundary_lsn
    }
}

pub open spec fn map_to_multiset<K, V>(m: Map<K, V>) -> Multiset<(K, V)>
{
    m.kv_pairs().to_multiset()
}

pub open spec fn valid_request_reply_pair(req: Request, reply: Reply) -> bool
{
    &&& req.id == reply.id
    &&& req.input is QueryInput <==> reply.output is QueryOutput
    &&& req.input is PutInput <==> reply.output is PutOutput
    &&& req.input is NoopInput <==> reply.output is NoopOutput
}

pub open spec(checked) fn to_map_label(req: Request, reply: Reply) -> MapSpec::Label
    recommends valid_request_reply_pair(req, reply)
{
    let input = req.input;
    let output = reply.output;
    match req.input {
        Input::QueryInput{..} => MapSpec::Label::Query{input, output},
        Input::PutInput{..} => MapSpec::Label::Put{input, output},
        Input::NoopInput{} => MapSpec::Label::Noop{input, output},
    }
}

pub open spec fn active_query_roots(active_branch: CachedBranch::State) -> Seq<Address>
{
    if active_branch.root is Some {
        seq![active_branch.root.unwrap()]
    } else {
        seq![]
    }
}

pub open spec fn query_roots(sealed_roots: Seq<Address>, active_branch: CachedBranch::State) -> Seq<Address>
{
    sealed_roots + active_query_roots(active_branch)
}

pub open spec fn query_from_receipts_up_to(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
) -> Message
    recommends
        end <= receipts.len(),
    decreases end
{
    if end == 0 {
        Message::Update{delta: nop_delta()}
    } else {
        let idx = (end - 1) as int;
        query_from_receipts_up_to(receipts, (end - 1) as nat).merge(receipts[idx].result())
    }
}

pub open spec fn query_receipts_valid(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    read_nodes: LoadedBranch,
    key: Key,
) -> bool
{
    &&& receipts.len() <= roots.len()
    &&& forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
        ==> {
            let receipt = receipts[i];
            let root_idx = roots.len() as int - receipts.len() as int + i;
            &&& receipt.key == key
            &&& receipt.valid_for(roots[root_idx], read_nodes)
            &&& receipt.target().node is Leaf
    }
    &&& receipts.len() < roots.len() ==>
        query_from_receipts_up_to(receipts, receipts.len() as nat) is Define
}

pub open spec fn query_receipts_read_addrs(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
) -> Set<Address>
    recommends
        end <= receipts.len(),
    decreases end
{
    if end == 0 {
        Set::empty()
    } else {
        let idx = (end - 1) as int;
        query_receipts_read_addrs(receipts, (end - 1) as nat) + receipts[idx].needed_addrs()
    }
}

impl AtomicJournalState::State {
    pub open spec fn empty() -> Self
    {
        AtomicJournalState::State{
            journal: CachedJournal::State{
                snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
                status: None,
            },
            mini_allocator: MiniAllocator::empty(),
            au_page_bounds: Map::empty(),
            persistent_seq_end: 0,
            in_flight: None,
            prepared: false,
        }
    }

    pub open spec fn ready(self) -> bool
    {
        self.journal.status is Some
    }

    pub open spec fn loaded_index_aus(self) -> Set<AU>
    {
        if self.journal.status is Some {
            self.journal.status.unwrap().lsn_au_index.values()
        } else {
            Set::empty()
        }
    }

    pub open spec fn owned_aus(self) -> Set<AU>
    {
        self.loaded_index_aus() + self.mini_allocator.all_aus()
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.journal.wf()
        &&& self.mini_allocator.wf()
        &&& self.in_flight is Some ==> self.in_flight.unwrap().wf()
        &&& self.prepared ==> self.in_flight is Some
    }

    pub proof fn wf_next(pre: Self, post: Self, lbl: AtomicJournalState::Label)
        requires
            pre.wf(),
            AtomicJournalState::State::next(pre, post, lbl),
        ensures
            post.wf(),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::put(new_journal) => {
                assert(AtomicJournalState::State::put(pre, post, lbl, new_journal));
                let messages = match lbl {
                    AtomicJournalState::Label::Put{messages} => messages,
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::Put{
                    messages,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::load_index(new_journal, au_depth, page_depth) => {
                assert(AtomicJournalState::State::load_index(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    au_depth,
                    page_depth,
                ));
                let (reads, discovered_aus) = match lbl {
                    AtomicJournalState::Label::LoadIndex{reads, discovered_aus} => (reads, discovered_aus),
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::LoadIndex{
                    reads,
                    discovered_aus,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::read_for_recovery(new_journal) => {
                assert(AtomicJournalState::State::read_for_recovery(pre, post, lbl, new_journal));
                let (messages, reads) = match lbl {
                    AtomicJournalState::Label::ReadForRecovery{messages, reads} => (messages, reads),
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::ReadForRecovery{
                    messages,
                    reads,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::journal_marshal(new_journal) => {
                assert(AtomicJournalState::State::journal_marshal(pre, post, lbl, new_journal));
                let (addr, writes) = match lbl {
                    AtomicJournalState::Label::JournalMarshal{addr, writes} => (addr, writes),
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::JournalMarshal{
                    writes,
                });
                assert(pre.mini_allocator.allocate(addr).wf());
                assert(pre.mini_allocator.allocate(addr).observe(addr).wf());
                assert(post.wf());
            },
            AtomicJournalState::Step::observe_clean_aus(new_journal) => {
                assert(AtomicJournalState::State::observe_clean_aus(pre, post, lbl, new_journal));
                let aus = match lbl {
                    AtomicJournalState::Label::ObserveCleanAUs{aus} => aus,
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::ObserveCleanAUs{
                    aus,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::fill_aus() => {
                assert(AtomicJournalState::State::fill_aus(pre, post, lbl));
                assert(post.mini_allocator.wf());
                assert(post.wf());
            },
            AtomicJournalState::Step::query_end_lsn() => {
                assert(AtomicJournalState::State::query_end_lsn(pre, post, lbl));
                assert(post == pre);
                assert(post.wf());
            },
            AtomicJournalState::Step::commit_start() => {
                assert(AtomicJournalState::State::commit_start(pre, post, lbl));
                assert(post.wf());
            },
            AtomicJournalState::Step::commit_prepared() => {
                assert(AtomicJournalState::State::commit_prepared(pre, post, lbl));
                assert(post == AtomicJournalState::State{
                    prepared: true,
                    ..pre
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::commit_complete(new_journal) => {
                assert(AtomicJournalState::State::commit_complete(pre, post, lbl, new_journal));
                let (require_end, discarded_aus) = match lbl {
                    AtomicJournalState::Label::CommitComplete{
                        require_end,
                        discarded_aus,
                    } => (require_end, discarded_aus),
                    _ => arbitrary(),
                };
                assert(pre.in_flight is Some);
                let image = pre.in_flight.unwrap();
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::DiscardOld{
                    start_lsn: image.snapshot.boundary_lsn,
                    require_end,
                    deallocs: discarded_aus,
                });
                pre.mini_allocator.prune_preserves_wf(discarded_aus);
                assert(post.wf());
            },
            AtomicJournalState::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    pub proof fn commit_complete_effect(
        pre: Self,
        post: Self,
        lbl: AtomicJournalState::Label,
    )
        requires
            pre.wf(),
            AtomicJournalState::State::next(pre, post, lbl),
            lbl is CommitComplete,
        ensures
            post.journal.status is Some,
            pre.journal.status is Some,
            post.journal.seq_end() == pre.journal.seq_end(),
            pre.in_flight is Some,
            post.persistent_seq_end == pre.in_flight.unwrap().seq_end,
            post.in_flight is None,
            post.prepared == false,
            post.mini_allocator == pre.mini_allocator.prune(lbl->discarded_aus),
            lbl->discarded_aus <= pre.owned_aus(),
            post.owned_aus() <= pre.owned_aus(),
            post.owned_aus().disjoint(lbl->discarded_aus),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::commit_complete(new_journal) => {
                assert(AtomicJournalState::State::commit_complete(pre, post, lbl, new_journal));
                let cj_lbl = CachedJournal::Label::DiscardOld{
                    start_lsn: pre.in_flight.unwrap().snapshot.boundary_lsn,
                    require_end: lbl->require_end,
                    deallocs: lbl->discarded_aus,
                };
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let cj_step = choose |cj_step|
                    CachedJournal::State::next_by(pre.journal, post.journal, cj_lbl, cj_step);
                match cj_step {
                    CachedJournal::Step::discard_old() => {
                        assert(CachedJournal::State::discard_old(pre.journal, post.journal, cj_lbl));
                        let old_index = pre.journal.status.unwrap().lsn_au_index;
                        let new_index = post.journal.status.unwrap().lsn_au_index;
                        assert(lbl->discarded_aus == old_index.values().difference(new_index.values()));
                        let start_lsn = pre.in_flight.unwrap().snapshot.boundary_lsn;
                        let new_tail = pre.journal.status.unwrap().unmarshalled_tail.bounded_discard(
                            start_lsn,
                        );
                        assert(post.journal.status.unwrap().unmarshalled_tail == new_tail);
                        if pre.journal.status.unwrap().unmarshalled_tail.seq_start <= start_lsn {
                            assert(new_tail.seq_end
                                == pre.journal.status.unwrap().unmarshalled_tail.seq_end);
                        } else {
                            assert(new_tail == pre.journal.status.unwrap().unmarshalled_tail);
                        }
                        pre.mini_allocator.prune_preserves_wf(lbl->discarded_aus);
                        assert(post.loaded_index_aus() == new_index.values());
                        assert(post.mini_allocator.all_aus()
                            == pre.mini_allocator.all_aus().difference(lbl->discarded_aus));
                        assert(lbl->discarded_aus <= pre.owned_aus());
                        assert(post.loaded_index_aus() <= pre.loaded_index_aus());
                        assert(post.mini_allocator.all_aus() <= pre.mini_allocator.all_aus());
                        assert(post.owned_aus() <= pre.owned_aus());
                        assert(post.loaded_index_aus().disjoint(lbl->discarded_aus));
                        assert(post.mini_allocator.all_aus().disjoint(lbl->discarded_aus));
                        assert(post.owned_aus().disjoint(lbl->discarded_aus));
                    },
                    _ => {
                        assert(false);
                    },
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn commit_start_effect(
        pre: Self,
        post: Self,
        lbl: AtomicJournalState::Label,
    )
        requires
            AtomicJournalState::State::next(pre, post, lbl),
            lbl is CommitStart,
        ensures
            post.journal == pre.journal,
            post.mini_allocator == pre.mini_allocator,
            post.persistent_seq_end == pre.persistent_seq_end,
            post.in_flight == Option::Some(AtomicJournalImage{
                snapshot: lbl->snapshot,
                seq_end: lbl->seq_end,
            }),
            post.prepared == false,
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::commit_start() => {
                assert(AtomicJournalState::State::commit_start(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }
}

impl AtomicBranchState::State {
    pub open spec fn empty() -> Self
    {
        AtomicBranchState::State{
            image: empty_branch_image(),
            persistent_image: empty_branch_image(),
            in_flight: None,
            prepared: false,
            branch_summary: Map::empty(),
            persisted_root_count: 0,
            active_branch: CachedBranch::State::empty_active(),
            mini_allocator: MiniAllocator::empty(),
            seq_end: 0,
        }
    }

    pub open spec fn owned_aus(self) -> Set<AU>
    {
        summary_aus(self.branch_summary) + self.mini_allocator.all_aus()
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.persisted_root_count <= self.image.sealed_roots.len()
        &&& self.image.seq_end <= self.seq_end
        &&& self.persistent_image.sealed_roots.len() <= self.image.sealed_roots.len()
        &&& self.image.sealed_roots.take(self.persistent_image.sealed_roots.len() as int)
            == self.persistent_image.sealed_roots
        &&& self.persistent_image.sealed_roots.len() <= self.persisted_root_count
        &&& self.persistent_image.seq_end <= self.seq_end
        &&& self.in_flight is Some ==> {
            let image = self.in_flight.unwrap();
            &&& image.sealed_roots.len() <= self.image.sealed_roots.len()
            &&& self.image.sealed_roots.take(image.sealed_roots.len() as int)
                == image.sealed_roots
            &&& image.seq_end <= self.seq_end
        }
        &&& self.prepared ==> self.in_flight is Some
        &&& self.active_branch.wf()
        &&& self.mini_allocator.wf()
    }

    pub open spec fn freeze_image(self) -> AtomicBranchImage
    {
        AtomicBranchImage{
            sealed_roots: self.image.sealed_roots,
            seq_end: self.seq_end,
        }
    }

    pub open spec fn metadata_loaded(self) -> bool
    {
        forall |i: int| #![trigger self.image.sealed_roots[i]]
            0 <= i < self.image.sealed_roots.len()
            ==> self.branch_summary.contains_key(self.image.sealed_roots[i].au)
    }

    pub open spec fn seq_end(self) -> nat
    {
        self.seq_end
    }

    pub open spec fn root_addrs(self) -> Set<Address>
    {
        let sealed_roots = self.image.sealed_roots.to_set();
        let active_roots = if self.active_branch.root is Some {
            set![self.active_branch.root.unwrap()]
        } else {
            Set::empty()
        };
        sealed_roots + active_roots
    }

    pub proof fn wf_next(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
        ensures
            post.wf(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::query() => {
                assert(AtomicBranchState::State::query(pre, post, lbl));
            },
            AtomicBranchState::Step::load_metadata() => {
                assert(AtomicBranchState::State::load_metadata(pre, post, lbl));
            },
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                ));
                assert(post.mini_allocator == pre.mini_allocator);
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
                let (keys, msgs, init_root, write_nodes) = match lbl {
                    AtomicBranchState::Label::Append{keys, msgs, init_root, write_nodes, ..} =>
                        (keys, msgs, init_root, write_nodes),
                    _ => arbitrary(),
                };
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(init_addr));
                assert(init_addr.wf());
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::grow(new_active_branch) => {
                assert(AtomicBranchState::State::grow(pre, post, lbl, new_active_branch));
                let (new_root_addr, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Grow{new_root_addr, read_nodes, write_nodes} =>
                        (new_root_addr, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Grow{
                    mini_allocator: pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::grow_step(),
                ));
                assert(CachedBranch::State::grow_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_root_addr));
                assert(new_root_addr.wf());
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::split(new_active_branch) => {
                assert(AtomicBranchState::State::split(pre, post, lbl, new_active_branch));
                let (new_child_addr, receipt, split_arg, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Split{
                        new_child_addr,
                        receipt,
                        split_arg,
                        read_nodes,
                        write_nodes,
                    } => (new_child_addr, receipt, split_arg, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Split{
                    mini_allocator: pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::split_step(),
                ));
                assert(CachedBranch::State::split_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                assert(new_child_addr.wf());
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::seal() => {
                assert(AtomicBranchState::State::seal(pre, post, lbl));
                pre.mini_allocator.prune_preserves_wf(lbl->summary);
                let n = pre.persistent_image.sealed_roots.len();
                assert(post.persistent_image == pre.persistent_image);
                assert(post.image.sealed_roots == pre.image.sealed_roots.push(pre.active_branch.root.unwrap()));
                assert(n <= pre.image.sealed_roots.len());
                assert forall |i: int| 0 <= i < n implies
                    post.image.sealed_roots[i] == pre.image.sealed_roots[i]
                by {
                    assert(post.image.sealed_roots[i] == pre.image.sealed_roots.push(pre.active_branch.root.unwrap())[i]);
                }
                assert(post.image.sealed_roots.take(n as int) == pre.image.sealed_roots.take(n as int));
            },
            AtomicBranchState::Step::fill_aus() => {
                assert(AtomicBranchState::State::fill_aus(pre, post, lbl));
                assert(post.mini_allocator.wf());
            },
            AtomicBranchState::Step::observe_persisted_roots() => {
                assert(AtomicBranchState::State::observe_persisted_roots(pre, post, lbl));
            },
            AtomicBranchState::Step::commit_start() => {
                assert(AtomicBranchState::State::commit_start(pre, post, lbl));
                let branch_image = match lbl {
                    AtomicBranchState::Label::CommitStart{branch_image} => branch_image,
                    _ => arbitrary(),
                };
                assert(post.image == pre.image);
                assert(post.persisted_root_count == pre.persisted_root_count);
                assert(post.in_flight == Option::Some(branch_image));
                if branch_image == pre.persistent_image {
                    assert(branch_image.sealed_roots.len() <= pre.image.sealed_roots.len());
                    assert(pre.image.sealed_roots.take(branch_image.sealed_roots.len() as int)
                        == branch_image.sealed_roots);
                    assert(branch_image.sealed_roots.len() <= pre.persisted_root_count);
                    assert(branch_image.seq_end <= pre.seq_end);
                    assert(post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)
                        == branch_image.sealed_roots);
                } else {
                    assert(branch_image == pre.freeze_image());
                    assert(branch_image.sealed_roots == pre.image.sealed_roots);
                    assert(branch_image.seq_end == pre.seq_end);
                    assert(branch_image.sealed_roots.len() == post.image.sealed_roots.len());
                    assert forall |i: int| 0 <= i < branch_image.sealed_roots.len() implies
                        post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)[i]
                            == branch_image.sealed_roots[i]
                    by {
                        assert(post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)[i]
                            == post.image.sealed_roots[i]);
                    }
                    assert(post.image.sealed_roots.take(branch_image.sealed_roots.len() as int)
                        == branch_image.sealed_roots);
                }
            },
            AtomicBranchState::Step::commit_prepared() => {
                assert(AtomicBranchState::State::commit_prepared(pre, post, lbl));
                assert(post == AtomicBranchState::State{
                    prepared: true,
                    ..pre
                });
            },
            AtomicBranchState::Step::commit_complete() => {
                assert(AtomicBranchState::State::commit_complete(pre, post, lbl));
                assert(pre.in_flight is Some);
                let image = pre.in_flight.unwrap();
                let n = image.sealed_roots.len();
                assert(post.persistent_image == image);
                assert(post.image.sealed_roots.take(n as int) == image.sealed_roots);
                assert(post.image.sealed_roots.take(post.persistent_image.sealed_roots.len() as int)
                    == post.persistent_image.sealed_roots);
            },
            AtomicBranchState::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
        if post.in_flight is Some {
            let image = post.in_flight.unwrap();
            match step {
                AtomicBranchState::Step::query() => {
                    assert(AtomicBranchState::State::query(pre, post, lbl));
                    assert(post == pre);
                },
                AtomicBranchState::Step::load_metadata() => {
                    assert(AtomicBranchState::State::load_metadata(pre, post, lbl));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                    assert(AtomicBranchState::State::append_nonempty(
                        pre,
                        post,
                        lbl,
                        new_active_branch,
                    ));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::append_empty(new_active_branch) => {
                    assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::grow(new_active_branch) => {
                    assert(AtomicBranchState::State::grow(pre, post, lbl, new_active_branch));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::split(new_active_branch) => {
                    assert(AtomicBranchState::State::split(pre, post, lbl, new_active_branch));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::seal() => {
                    assert(AtomicBranchState::State::seal(pre, post, lbl));
                    assert(post.in_flight == pre.in_flight);
                    let n = image.sealed_roots.len();
                    assert(n <= pre.image.sealed_roots.len());
                    assert(pre.image.sealed_roots.take(n as int) == image.sealed_roots);
                    assert(post.image.sealed_roots == pre.image.sealed_roots.push(pre.active_branch.root.unwrap()));
                    assert forall |i: int| 0 <= i < n implies
                        post.image.sealed_roots[i] == pre.image.sealed_roots[i]
                    by {
                        assert(post.image.sealed_roots[i] == pre.image.sealed_roots.push(pre.active_branch.root.unwrap())[i]);
                    }
                    assert(post.image.sealed_roots.take(n as int) == pre.image.sealed_roots.take(n as int));
                    assert(post.image.sealed_roots.take(n as int) == image.sealed_roots);
                },
                AtomicBranchState::Step::fill_aus() => {
                    assert(AtomicBranchState::State::fill_aus(pre, post, lbl));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::observe_persisted_roots() => {
                    assert(AtomicBranchState::State::observe_persisted_roots(pre, post, lbl));
                    assert(post.image == pre.image);
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::commit_start() => {
                    assert(AtomicBranchState::State::commit_start(pre, post, lbl));
                    let branch_image = match lbl {
                        AtomicBranchState::Label::CommitStart{branch_image} => branch_image,
                        _ => arbitrary(),
                    };
                    assert(image == branch_image);
                },
                AtomicBranchState::Step::commit_prepared() => {
                    assert(AtomicBranchState::State::commit_prepared(pre, post, lbl));
                    assert(post == AtomicBranchState::State{
                        prepared: true,
                        ..pre
                    });
                    assert(post.in_flight == pre.in_flight);
                },
                AtomicBranchState::Step::commit_complete() => {
                    assert(false);
                },
                AtomicBranchState::Step::dummy_to_use_type_params(_) => {
                    assert(false);
                },
            }
        }
        assert(post.wf());
    }

    pub proof fn append_preserves_owned_aus(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Append,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.mini_allocator.all_aus() == pre.mini_allocator.all_aus(),
            post.owned_aus() == pre.owned_aus(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                ));
                assert(post.branch_summary == pre.branch_summary);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(post.owned_aus() == pre.owned_aus());
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
                assert(post.branch_summary == pre.branch_summary);
                let (keys, msgs, init_root, write_nodes) = match lbl {
                    AtomicBranchState::Label::Append{keys, msgs, init_root, write_nodes, ..} =>
                        (keys, msgs, init_root, write_nodes),
                    _ => arbitrary(),
                };
                assert(init_root is Some);
                let init_addr = init_root.unwrap();
                let branch_lbl = CachedBranch::Label::Initialize{
                    mini_allocator: pre.mini_allocator,
                    init_root: init_addr,
                    keys,
                    msgs,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::initialize_branch(),
                ));
                assert(CachedBranch::State::initialize_branch(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(init_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    init_addr,
                );
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(post.owned_aus() == pre.owned_aus());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn append_effect(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Append,
        ensures
            post.image == pre.image,
            post.persistent_image == pre.persistent_image,
            post.in_flight == pre.in_flight,
            post.branch_summary == pre.branch_summary,
            post.persisted_root_count == pre.persisted_root_count,
            post.seq_end == pre.seq_end + lbl->keys.len(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                ));
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn grow_preserves_backing_aus(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Grow,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.mini_allocator.all_aus() == pre.mini_allocator.all_aus(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::grow(new_active_branch) => {
                assert(AtomicBranchState::State::grow(pre, post, lbl, new_active_branch));
                let (new_root_addr, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Grow{new_root_addr, read_nodes, write_nodes} =>
                        (new_root_addr, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Grow{
                    mini_allocator: pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::grow_step(),
                ));
                assert(CachedBranch::State::grow_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_root_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    new_root_addr,
                );
            },
            _ => { assert(false); },
        }
    }

    pub proof fn split_preserves_backing_aus(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            pre.wf(),
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Split,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.mini_allocator.all_aus() == pre.mini_allocator.all_aus(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::split(new_active_branch) => {
                assert(AtomicBranchState::State::split(pre, post, lbl, new_active_branch));
                let (new_child_addr, receipt, split_arg, read_nodes, write_nodes) = match lbl {
                    AtomicBranchState::Label::Split{
                        new_child_addr,
                        receipt,
                        split_arg,
                        read_nodes,
                        write_nodes,
                    } => (new_child_addr, receipt, split_arg, read_nodes, write_nodes),
                    _ => arbitrary(),
                };
                let branch_lbl = CachedBranch::Label::Split{
                    mini_allocator: pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                assert(CachedBranch::State::next_by(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                    CachedBranch::Step::split_step(),
                ));
                assert(CachedBranch::State::split_step(
                    pre.active_branch,
                    new_active_branch,
                    branch_lbl,
                ));
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                crate::implementation::AllocationBranchStack_v::mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    new_child_addr,
                );
            },
            _ => { assert(false); },
        }
    }

    pub proof fn append_support_effect(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is Append,
        ensures
            atomic_branch_support_addrs(pre) <= atomic_branch_support_addrs(post),
            ({
                let write_nodes = match lbl {
                    AtomicBranchState::Label::Append{write_nodes, ..} => write_nodes,
                    _ => arbitrary(),
                };
                write_nodes.dom() <= atomic_branch_support_addrs(post)
            }),
            ({
                let write_nodes = match lbl {
                    AtomicBranchState::Label::Append{write_nodes, ..} => write_nodes,
                    _ => arbitrary(),
                };
                atomic_branch_support_addrs(post) <= atomic_branch_support_addrs(pre) + write_nodes.dom()
            }),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                assert(AtomicBranchState::State::append_nonempty(
                    pre,
                    post,
                    lbl,
                    new_active_branch,
                )) by {
                    reveal(AtomicBranchState::State::append_nonempty);
                }
                let write_nodes = match lbl {
                    AtomicBranchState::Label::Append{write_nodes, ..} => write_nodes,
                    _ => arbitrary(),
                };
                assert(post.branch_summary == pre.branch_summary);
                assert(atomic_branch_support_addrs(post)
                    == addresses_in_aus(summary_aus(pre.branch_summary))
                        + mini_allocator_allocated_addrs(post.mini_allocator));
                assert(atomic_branch_support_addrs(pre) <= atomic_branch_support_addrs(post));
                assert(write_nodes.dom() <= atomic_branch_support_addrs(post));
                assert(atomic_branch_support_addrs(post)
                    <= atomic_branch_support_addrs(pre) + write_nodes.dom());
            },
            AtomicBranchState::Step::append_empty(new_active_branch) => {
                assert(AtomicBranchState::State::append_empty(pre, post, lbl, new_active_branch)) by {
                    reveal(AtomicBranchState::State::append_empty);
                }
                let write_nodes = match lbl {
                    AtomicBranchState::Label::Append{write_nodes, ..} => write_nodes,
                    _ => arbitrary(),
                };
                assert(post.branch_summary == pre.branch_summary);
                assert(atomic_branch_support_addrs(post)
                    == addresses_in_aus(summary_aus(pre.branch_summary))
                        + mini_allocator_allocated_addrs(post.mini_allocator));
                assert(atomic_branch_support_addrs(pre) <= atomic_branch_support_addrs(post));
                assert(write_nodes.dom() <= atomic_branch_support_addrs(post));
                assert(atomic_branch_support_addrs(post)
                    <= atomic_branch_support_addrs(pre) + write_nodes.dom());
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn fill_aus_effect(pre: Self, post: Self, lbl: AtomicBranchState::Label)
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is FillAUs,
        ensures
            post.image == pre.image,
            post.persistent_image == pre.persistent_image,
            post.in_flight == pre.in_flight,
            post.branch_summary == pre.branch_summary,
            post.persisted_root_count == pre.persisted_root_count,
            post.active_branch == pre.active_branch,
            post.seq_end == pre.seq_end,
            post.mini_allocator == pre.mini_allocator.add_aus(lbl->aus),
            post.metadata_loaded() == pre.metadata_loaded(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::fill_aus() => {
                assert(AtomicBranchState::State::fill_aus(pre, post, lbl)) by {
                    reveal(AtomicBranchState::State::fill_aus);
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn commit_complete_effect(
        pre: Self,
        post: Self,
        lbl: AtomicBranchState::Label,
    )
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is CommitComplete,
        ensures
            post.image == pre.image,
            post.branch_summary == pre.branch_summary,
            post.active_branch == pre.active_branch,
            post.mini_allocator == pre.mini_allocator,
            post.seq_end == pre.seq_end,
            pre.in_flight is Some,
            post.in_flight is None,
            post.prepared == false,
            post.persistent_image == pre.in_flight.unwrap(),
            post.owned_aus() == pre.owned_aus(),
            post.metadata_loaded() == pre.metadata_loaded(),
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::commit_complete() => {
                assert(AtomicBranchState::State::commit_complete(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn commit_start_effect(
        pre: Self,
        post: Self,
        lbl: AtomicBranchState::Label,
    )
        requires
            AtomicBranchState::State::next(pre, post, lbl),
            lbl is CommitStart,
        ensures
            post.image == pre.image,
            post.persistent_image == pre.persistent_image,
            post.branch_summary == pre.branch_summary,
            post.persisted_root_count == pre.persisted_root_count,
            post.active_branch == pre.active_branch,
            post.mini_allocator == pre.mini_allocator,
            post.seq_end == pre.seq_end,
            post.in_flight == Option::Some(lbl->branch_image),
            post.prepared == false,
    {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        let step = choose |step| AtomicBranchState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicBranchState::Step::commit_start() => {
                assert(AtomicBranchState::State::commit_start(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }
}

impl AtomicInflightInfo {
    pub open spec fn wf(self) -> bool
    {
        true
    }
}

impl AnotherAtomicState {
    pub open spec fn reserved_aus() -> Set<AU>
    {
        set![spec_superblock_addr().au]
    }

    pub open spec fn init(cache_slots: nat, free_aus: Set<AU>) -> Self
    {
        AnotherAtomicState{
            recovery_state: RecoveryState::Begin,
            cache: Cache::State::empty(cache_slots),
            outstanding_cache_reqs: Map::empty(),
            free_aus,
            journal: AtomicJournalState::State::empty(),
            branch: AtomicBranchState::State::empty(),
            persistent_image: None,
            in_flight: None,
            sync_req_map: Map::empty(),
        }
    }

    pub open spec fn journal_metadata_loaded(self) -> bool
    {
        self.journal.ready()
    }

    pub open spec fn branch_metadata_loaded(self) -> bool
    {
        self.branch.metadata_loaded()
    }

    pub open spec fn client_ready(self) -> bool
    {
        self.recovery_state is RecoveryComplete
    }

    pub open spec fn superblock_metadata_known(self) -> bool
    {
        self.persistent_image is Some
    }

    pub open spec fn atomic_inflight_superblock_i(self) -> AbstractSuperblockImage
    {
        let journal_image = self.journal.in_flight.unwrap();
        let branch_image = self.branch.in_flight.unwrap();
        AbstractSuperblockImage{
            journal_snapshot: journal_image.snapshot,
            journal_seq_end: journal_image.seq_end,
            branch_roots: branch_image.sealed_roots,
            branch_seq_end: self.in_flight.unwrap().boundary_lsn,
        }
    }

    pub open spec fn in_flight_agrees(self) -> bool
    {
        &&& (self.in_flight is Some <==> self.journal.in_flight is Some)
        &&& (self.in_flight is Some <==> self.branch.in_flight is Some)
        &&& self.in_flight is Some ==> {
            let boundary_lsn = self.in_flight.unwrap().boundary_lsn;
            &&& self.journal.in_flight.unwrap().snapshot.boundary_lsn == boundary_lsn
            &&& self.branch.in_flight.unwrap().seq_end == boundary_lsn
            &&& self.atomic_inflight_superblock_i().wf()
        }
    }

    pub open spec fn journal_owned_aus(self) -> Set<AU>
    {
        self.journal.owned_aus()
    }

    pub open spec fn branch_owned_aus(self) -> Set<AU>
    {
        self.branch.owned_aus()
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

    pub open spec fn recovery_metadata_wf(self) -> bool
    {
        &&& self.recovery_state is SuperblockAvailable ==> self.superblock_metadata_known()
        &&& self.recovery_state is MetadataLoadComplete ==> {
            &&& self.superblock_metadata_known()
            &&& self.journal_metadata_loaded()
            &&& self.branch_metadata_loaded()
        }
        &&& self.recovery_state is RecoveryComplete ==> {
            &&& self.superblock_metadata_known()
            &&& self.journal_metadata_loaded()
            &&& self.branch_metadata_loaded()
            &&& self.journal.journal.seq_end() == self.branch.seq_end()
        }
    }

    pub open spec fn sync_image_metadata_valid(self, image: AbstractSuperblockImage) -> bool
    {
        let root_count = image.branch_roots.len() as nat;
        &&& image.wf()
        &&& self.journal.persistent_seq_end <= image.journal_seq_end
        &&& image.journal_seq_end <= self.journal.journal.seq_end()
        &&& image.branch_seq_end <= self.branch.seq_end()
        &&& root_count <= self.branch.persisted_root_count
        &&& root_count <= self.branch.image.sealed_roots.len()
        &&& self.branch.image.sealed_roots.take(root_count as int) == image.branch_roots
    }

    pub open spec fn cache_request_wf(self) -> bool
    {
        &&& self.outstanding_cache_reqs.is_injective()
        &&& !self.outstanding_cache_reqs.contains_value(spec_superblock_addr())
        &&& self.outstanding_cache_reqs.values() <= self.cache.lookup_map.dom()
        &&& forall |id: ID| #[trigger] self.outstanding_cache_reqs.contains_key(id) ==> {
            let addr = self.outstanding_cache_reqs[id];
            let slot = self.cache.lookup_map[addr];
            match self.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && self.cache.status_map[slot] is Writeback,
                _ => false,
            }
        }
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.cache.inv()
        &&& self.cache_request_wf()
        &&& self.journal.wf()
        &&& self.branch.wf()
        &&& self.allocation_wf()
        &&& self.recovery_metadata_wf()
        &&& self.in_flight_agrees()
        &&& self.in_flight is Some ==> self.in_flight.unwrap().wf()
        &&& !(self.recovery_state is RecoveryComplete) ==> self.in_flight is None
    }

    pub open spec fn execute_noop(pre: Self, post: Self, req: Request, reply: Reply) -> bool
    {
        &&& post == pre
    }

    pub open spec fn execute_put(
        pre: Self,
        post: Self,
        req: Request,
        reply: Reply,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    ) -> bool
    {
        let key = req.input.arrow_PutInput_key();
        let value = req.input.arrow_PutInput_value();
        let msg = Message::Define{value};
        let keyed_message = KeyedMessage{key, message: msg};
        let records = MsgHistory::singleton_at(pre.branch.seq_end(), keyed_message);
        let keys = seq![key];
        let msgs = seq![msg];
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Append{
            keys,
            msgs,
            receipt,
            init_root,
            read_nodes,
            write_nodes,
        };

        &&& pre.client_ready()
        &&& req.input is PutInput
        &&& reply.output is PutOutput
        &&& AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::Put{messages: records},
        )
        &&& writes.dom() =~= write_nodes.dom()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(
            pre.branch,
            branch,
            branch_lbl,
        )
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            branch,
            ..pre
        }
    }

    pub open spec fn execute_query(
        pre: Self,
        post: Self,
        req: Request,
        reply: Reply,
        end_lsn: LSN,
        key: Key,
        value: Value,
        msg: Message,
        receipts: Seq<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    ) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
        let read_nodes = to_branch_nodes(reads);
        let branch_lbl = AtomicBranchState::Label::Query{key, msg, receipts, read_nodes};
        &&& pre.client_ready()
        &&& reads.dom() == query_receipts_read_addrs(receipts, receipts.len() as nat)
        &&& req.input is QueryInput
        &&& reply.output is QueryOutput
        &&& key == req.input.arrow_QueryInput_key()
        &&& value == reply.output.arrow_QueryOutput_value()
        &&& end_lsn == pre.branch.seq_end()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(pre.branch, pre.branch, branch_lbl)
        &&& normalize_value(msg) == value
        &&& post == Self{cache: post.cache, ..pre}
    }

    pub open spec fn execute_transition(
        pre: Self,
        post: Self,
        req: Request,
        reply: Reply,
        event: ProgramEvent,
    ) -> bool
    {
        &&& valid_request_reply_pair(req, reply)
        &&& match req.input {
            Input::NoopInput{} => event is NoOp,
            Input::QueryInput{..} => event is Query,
            Input::PutInput{..} => event is Put,
        }
        &&& match event {
            ProgramEvent::NoOp{} => Self::execute_noop(pre, post, req, reply),
            ProgramEvent::Put{receipt, init_root, reads, writes, branch} =>
                Self::execute_put(pre, post, req, reply, receipt, init_root, reads, writes, branch),
            ProgramEvent::Query{end_lsn, key, value, msg, receipts, reads} =>
                Self::execute_query(pre, post, req, reply, end_lsn, key, value, msg, receipts, reads),
        }
    }

    pub open spec fn journal_load_index(
        pre: Self,
        post: Self,
        cache_reads: Map<Address, RawPage>,
        journal_reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
    ) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads: cache_reads, writes: Map::empty()};
        let journal_lbl = AtomicJournalState::Label::LoadIndex{
            reads: to_journal_records(journal_reads),
            discovered_aus,
        };
        &&& pre.recovery_state is SuperblockAvailable
        &&& journal_reads <= cache_reads
        &&& to_aus(journal_reads.dom()) <= discovered_aus
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicJournalState::State::next(pre.journal, post.journal, journal_lbl)
        &&& post == Self{
            cache: post.cache,
            free_aus: pre.free_aus - discovered_aus,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn read_for_recovery(
        pre: Self,
        post: Self,
        addr: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        journal_reads: Map<Address, RawPage>,
        branch_reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    ) -> bool
    {
        let reads = journal_reads.union_prefer_right(branch_reads);
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(branch_reads);
        let write_nodes = to_branch_nodes(writes);
        &&& pre.recovery_state is MetadataLoadComplete
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& journal_reads <= reads
        &&& branch_reads <= reads
        &&& journal_reads.contains_key(addr)
        &&& branch_reads.dom() <= atomic_branch_support_addrs(pre.branch)
        &&& branch_reads.dom() <= Set::new(|addr: Address| addr.wf())
        &&& writes.dom() <= Set::new(|addr: Address| addr.wf())
        &&& pre.branch.seq_end() + keys.len() <= pre.journal.journal.seq_end()
        &&& {
            let journal_records = to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
                pre.journal.journal.snapshot.boundary_lsn,
            );
            let branch_records = to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
                pre.journal.journal.seq_start(),
            );
            let journal_lbl = AtomicJournalState::Label::ReadForRecovery{
                messages: journal_records,
                reads: to_journal_records(journal_reads),
            };
            &&& branch_records == append_puts(pre.branch.seq_end(), keys, msgs)
            &&& AtomicJournalState::State::next(pre.journal, post.journal, journal_lbl)
        }
        &&& AtomicBranchState::State::next(
            pre.branch,
            branch,
            AtomicBranchState::Label::Append{
                keys,
                msgs,
                receipt,
                init_root,
                read_nodes,
                write_nodes,
            },
        )
        &&& writes.dom() =~= write_nodes.dom()
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            branch,
            ..pre
        }
    }

    pub open spec fn journal_marshall(
        pre: Self,
        post: Self,
        addr: Address,
        raw_page: RawPage,
    ) -> bool
    {
        let writes = Map::<Address, RawPage>::empty().insert(addr, raw_page);
        let journal_lbl = AtomicJournalState::Label::JournalMarshal{
            addr,
            writes: to_journal_records(writes),
        };
        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes};
        &&& pre.client_ready()
        &&& AtomicJournalState::State::next(pre.journal, post.journal, journal_lbl)
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn acknowledge_flushed_journal_aus(
        pre: Self,
        post: Self,
        aus: Set<AU>,
    ) -> bool
    {
        let cache_lbl = Cache::Label::EvictableCheck{aus};
        let journal_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};
        &&& pre.client_ready()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicJournalState::State::next(pre.journal, post.journal, journal_lbl)
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn journal_fill_aus(pre: Self, post: Self, aus: Set<AU>) -> bool
    {
        &&& pre.client_ready()
        &&& aus <= pre.free_aus
        &&& AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::FillAUs{aus},
        )
        &&& post == Self{
            free_aus: pre.free_aus - aus,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn branch_load_metadata(
        pre: Self,
        post: Self,
        root: Address,
        reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
    ) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
        let read_nodes = to_branch_nodes(reads);
        let branch_lbl = AtomicBranchState::Label::LoadMetadata{root, discovered_aus, read_nodes};
        &&& pre.recovery_state is SuperblockAvailable
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(pre.branch, post.branch, branch_lbl)
        &&& post == Self{
            cache: post.cache,
            free_aus: pre.free_aus - discovered_aus,
            branch: post.branch,
            ..pre
        }
    }

    pub open spec fn metadata_load_complete(
        pre: Self,
        post: Self,
    ) -> bool
    {
        &&& pre.recovery_state is SuperblockAvailable
        &&& pre.journal_metadata_loaded()
        &&& pre.branch_metadata_loaded()
        &&& pre.branch.mini_allocator == MiniAllocator::empty()
        &&& post == Self{
            recovery_state: RecoveryState::MetadataLoadComplete,
            ..pre
        }
    }

    pub open spec fn branch_fill_aus(pre: Self, post: Self, aus: Set<AU>) -> bool
    {
        &&& pre.client_ready()
        &&& aus <= pre.free_aus
        &&& AtomicBranchState::State::next(
            pre.branch,
            post.branch,
            AtomicBranchState::Label::FillAUs{aus},
        )
        &&& post == Self{
            free_aus: pre.free_aus - aus,
            branch: post.branch,
            ..pre
        }
    }

    pub open spec fn branch_grow(
        pre: Self,
        post: Self,
        new_root_addr: Address,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    ) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Grow{
            new_root_addr,
            read_nodes,
            write_nodes,
        };
        &&& pre.client_ready()
        &&& reads.dom() == set![pre.branch.active_branch.root.unwrap()]
        &&& writes.dom() =~= write_nodes.dom()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(pre.branch, branch, branch_lbl)
        &&& post == Self{
            cache: post.cache,
            branch,
            ..pre
        }
    }

    pub open spec fn branch_split(
        pre: Self,
        post: Self,
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    ) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Split{
            new_child_addr,
            receipt,
            split_arg,
            read_nodes,
            write_nodes,
        };
        &&& pre.client_ready()
        &&& reads.dom() == split_read_addrs(receipt)
        &&& reads.dom() <= atomic_branch_support_addrs(pre.branch)
        &&& reads.dom() <= Set::new(|addr: Address| addr.wf())
        &&& writes.dom() =~= write_nodes.dom()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(pre.branch, branch, branch_lbl)
        &&& post == Self{
            cache: post.cache,
            branch,
            ..pre
        }
    }

    pub open spec fn branch_seal(
        pre: Self,
        post: Self,
        aux_ptr: Pointer,
        summary: Summary,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    ) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Seal{
            aux_ptr,
            summary,
            read_nodes,
            write_nodes,
        };
        &&& pre.client_ready()
        &&& writes.dom() =~= write_nodes.dom()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(pre.branch, branch, branch_lbl)
        &&& post == Self{
            cache: post.cache,
            branch,
            ..pre
        }
    }

    pub open spec fn observe_persisted_branch_roots(
        pre: Self,
        post: Self,
        target_count: nat,
        aus: Set<AU>,
    ) -> bool
    {
        let cache_lbl = Cache::Label::EvictableCheck{aus};
        let branch_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};
        &&& pre.client_ready()
        &&& aus == sealed_summary_aus_between(
            pre.branch.image.sealed_roots,
            pre.branch.branch_summary,
            pre.branch.persisted_root_count,
            target_count,
        )
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicBranchState::State::next(pre.branch, post.branch, branch_lbl)
        &&& post == Self{
            cache: post.cache,
            branch: post.branch,
            ..pre
        }
    }

    pub open spec fn cache_internal(pre: Self, post: Self) -> bool
    {
        &&& Cache::State::next(pre.cache, post.cache, Cache::Label::Internal{})
        &&& post == Self{cache: post.cache, ..pre}
    }

    pub open spec fn cache_io_begin(
        pre: Self,
        post: Self,
        req_map: Map<ID, DiskRequest>,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) -> bool
    {
        let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
        let new_outstanding = pre.outstanding_cache_reqs.union_prefer_right(updated);
        &&& updated.is_injective()
        &&& !updated.contains_value(spec_superblock_addr())
        &&& crate::implementation::MultisetMapRelation_v::multiset_to_map(reqs) == req_map
        &&& resps.is_empty()
        &&& Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        )
        &&& post == Self{
            cache: post.cache,
            outstanding_cache_reqs: new_outstanding,
            ..pre
        }
    }

    pub open spec fn cache_io_end(
        pre: Self,
        post: Self,
        resp_map: Map<ID, DiskResponse>,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) -> bool
    {
        let new_outstanding = pre.outstanding_cache_reqs.remove_keys(resp_map.dom());
        let finished = pre.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
        let cache_resps = Map::new(|addr| finished.contains_key(addr), |addr| resp_map[finished[addr]]);
        &&& reqs.is_empty()
        &&& crate::implementation::MultisetMapRelation_v::multiset_to_map(resps) == resp_map
        &&& Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
        )
        &&& post == Self{
            cache: post.cache,
            outstanding_cache_reqs: new_outstanding,
            ..pre
        }
    }

    pub proof fn cache_request_wf_preserved_by_unchanged(pre: Self, post: Self)
        requires
            pre.cache_request_wf(),
            post.cache == pre.cache,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            post.cache_request_wf(),
    {
        assert(post.outstanding_cache_reqs.is_injective());
        assert(!post.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
        assert(post.outstanding_cache_reqs.values() <= post.cache.lookup_map.dom());
        assert forall |id: ID| #[trigger] post.outstanding_cache_reqs.contains_key(id) implies {
            let addr = post.outstanding_cache_reqs[id];
            let slot = post.cache.lookup_map[addr];
            match post.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && post.cache.status_map[slot] is Writeback,
                _ => false,
            }
        } by {
            assert(pre.outstanding_cache_reqs.contains_key(id));
            let addr = pre.outstanding_cache_reqs[id];
            let slot = pre.cache.lookup_map[addr];
            assert(match pre.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre.cache.status_map[slot] is Writeback,
                _ => false,
            });
        }
    }

    pub proof fn cache_request_wf_preserved_by_cache_access(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.cache.inv(),
            pre.cache_request_wf(),
            Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            post.cache_request_wf(),
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes},
            Cache::Step::access(),
        ));
        assert(post.outstanding_cache_reqs.is_injective());
        assert(!post.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
        assert forall |addr: Address| post.outstanding_cache_reqs.values().contains(addr)
            implies post.cache.lookup_map.dom().contains(addr)
        by {
            let id = choose |id: ID| post.outstanding_cache_reqs.contains_key(id)
                && post.outstanding_cache_reqs[id] == addr;
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(pre.cache.lookup_map.dom().contains(addr));
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    assert(pre.cache.valid_write(addr));
                    let slot = pre.cache.lookup_map[addr];
                    assert(match pre.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && pre.cache.status_map[slot] is Writeback,
                        _ => false,
                    });
                    match pre.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => {
                            assert(!(pre.cache.valid_write(addr)));
                        },
                        Entry::Filled{addr: entry_addr, ..} => {
                            assert(pre.cache.status_map[slot] is Writeback);
                            assert(!(pre.cache.valid_write(addr)));
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(false);
                }
            };
            Cache::State::access_unwritten_addr_unchanged(
                pre.cache, post.cache, reads, writes, addr,
            );
            assert(post.cache.lookup_map.contains_key(addr));
        }
        assert(post.outstanding_cache_reqs.values() <= post.cache.lookup_map.dom());
        assert forall |id: ID| #[trigger] post.outstanding_cache_reqs.contains_key(id) implies {
            let addr = post.outstanding_cache_reqs[id];
            let slot = post.cache.lookup_map[addr];
            match post.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && post.cache.status_map[slot] is Writeback,
                _ => false,
            }
        } by {
            let addr = post.outstanding_cache_reqs[id];
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    assert(pre.cache.valid_write(addr));
                    let slot = pre.cache.lookup_map[addr];
                    assert(match pre.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && pre.cache.status_map[slot] is Writeback,
                        _ => false,
                    });
                    match pre.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => {
                            assert(!(pre.cache.valid_write(addr)));
                        },
                        Entry::Filled{addr: entry_addr, ..} => {
                            assert(pre.cache.status_map[slot] is Writeback);
                            assert(!(pre.cache.valid_write(addr)));
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(false);
                }
            };
            Cache::State::access_unwritten_addr_unchanged(
                pre.cache, post.cache, reads, writes, addr,
            );
            let pre_slot = pre.cache.lookup_map[addr];
            let post_slot = post.cache.lookup_map[addr];
            assert(post_slot == pre_slot);
            assert(post.cache.entries[post_slot] == pre.cache.entries[pre_slot]);
            assert(post.cache.status_map[post_slot] == pre.cache.status_map[pre_slot]);
            assert(match pre.cache.entries[pre_slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre.cache.status_map[pre_slot] is Writeback,
                _ => false,
            });
        }
    }

    pub proof fn cache_request_wf_preserved_by_cache_internal(pre: Self, post: Self)
        requires
            pre.cache.inv(),
            pre.cache_request_wf(),
            Cache::State::next(pre.cache, post.cache, Cache::Label::Internal{}),
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            post.cache_request_wf(),
    {
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Internal{});
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step: Cache::Step| Cache::State::next_by(
            pre.cache,
            post.cache,
            Cache::Label::Internal{},
            step,
        );
        match step {
            Cache::Step::reserve(new_slots_mapping) => {
                assert(Cache::State::reserve(
                    pre.cache,
                    post.cache,
                    Cache::Label::Internal{},
                    new_slots_mapping,
                ));
                let new_addr_slots = new_slots_mapping.invert();
                assert(new_slots_mapping.values().disjoint(pre.cache.lookup_map.dom()));
                assert(post.cache.lookup_map == pre.cache.lookup_map.union_prefer_right(new_addr_slots));
                pre.cache.build_lookup_map_ensures();
                assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                assert(post.outstanding_cache_reqs.is_injective());
                assert(!post.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
                assert forall |addr: Address| post.outstanding_cache_reqs.values().contains(addr)
                    implies post.cache.lookup_map.dom().contains(addr)
                by {
                    assert(pre.outstanding_cache_reqs.values().contains(addr));
                    assert(pre.cache.lookup_map.dom().contains(addr));
                    assert(!new_addr_slots.contains_key(addr)) by {
                        if new_addr_slots.contains_key(addr) {
                            assert(new_slots_mapping.contains_value(addr));
                            assert(false);
                        }
                    }
                    assert(post.cache.lookup_map.contains_key(addr));
                }
                assert(post.outstanding_cache_reqs.values() <= post.cache.lookup_map.dom());
                assert forall |id: ID| #[trigger] post.outstanding_cache_reqs.contains_key(id) implies {
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = post.cache.lookup_map[addr];
                    match post.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && post.cache.status_map[slot] is Writeback,
                        _ => false,
                    }
                } by {
                    let addr = post.outstanding_cache_reqs[id];
                    assert(pre.outstanding_cache_reqs.contains_key(id));
                    let old_slot = pre.cache.lookup_map[addr];
                    assert(pre.cache.lookup_map.contains_key(addr));
                    assert(pre.cache.entries.contains_key(old_slot)) by {
                        assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                    }
                    assert(!new_addr_slots.contains_key(addr)) by {
                        if new_addr_slots.contains_key(addr) {
                            assert(new_slots_mapping.contains_value(addr));
                            assert(false);
                        }
                    }
                    assert(post.cache.lookup_map[addr] == old_slot);
                    assert(!new_slots_mapping.contains_key(old_slot)) by {
                        if new_slots_mapping.contains_key(old_slot) {
                            assert(pre.cache.valid_new_slots_mapping(new_slots_mapping));
                            assert(pre.cache.entries[old_slot] is Empty);
                            assert(match pre.cache.entries[old_slot] {
                                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                                Entry::Filled{addr: entry_addr, ..} =>
                                    entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                                _ => false,
                            });
                            assert(false);
                        }
                    }
                    let updated_entries = Map::new(
                        |slot| new_slots_mapping.contains_key(slot),
                        |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                    );
                    assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                    assert(!updated_entries.contains_key(old_slot));
                    assert(!updated_entries.dom().contains(old_slot));
                    assert(pre.cache.entries.contains_key(old_slot));
                    assert(post.cache.status_map == pre.cache.status_map);
                    assert(pre.cache.entries.union_prefer_right(updated_entries)[old_slot]
                        == pre.cache.entries[old_slot]);
                    assert(post.cache.entries[old_slot] == pre.cache.entries[old_slot]);
                    assert(post.cache.status_map[old_slot] == pre.cache.status_map[old_slot]);
                    assert(match pre.cache.entries[old_slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                        _ => false,
                    });
                }
            },
            Cache::Step::evict(evicted_slots) => {
                assert(Cache::State::evict(
                    pre.cache,
                    post.cache,
                    Cache::Label::Internal{},
                    evicted_slots,
                ));
                let evicted_addrs = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| pre.cache.entries[slot].get_addr(),
                ).values();
                assert(post.cache.lookup_map == pre.cache.lookup_map.remove_keys(evicted_addrs));
                pre.cache.build_lookup_map_ensures();
                assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                assert(post.outstanding_cache_reqs.is_injective());
                assert(!post.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
                assert forall |addr: Address| post.outstanding_cache_reqs.values().contains(addr)
                    implies post.cache.lookup_map.dom().contains(addr)
                by {
                    assert(pre.outstanding_cache_reqs.values().contains(addr));
                    assert(pre.cache.lookup_map.dom().contains(addr));
                    let old_slot = pre.cache.lookup_map[addr];
                    assert(match pre.cache.entries[old_slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                        _ => false,
                    });
                    assert(!evicted_addrs.contains(addr)) by {
                        if evicted_addrs.contains(addr) {
                            let evicted_map = Map::new(
                                |slot| evicted_slots.contains(slot),
                                |slot| pre.cache.entries[slot].get_addr(),
                            );
                            let evicted_slot = choose |slot: Slot|
                                evicted_map.contains_key(slot) && evicted_map[slot] == addr;
                            assert(evicted_slots.contains(evicted_slot));
                            assert(pre.cache.entries[evicted_slot].get_addr() == addr);
                            assert(pre.cache.entries[evicted_slot] is Filled);
                            assert(pre.cache.status_map[evicted_slot] is Clean);
                            assert(pre.cache.lookup_map[addr] == evicted_slot);
                            assert(old_slot == evicted_slot);
                            match pre.cache.entries[old_slot] {
                                Entry::Loading{..} => {
                                    assert(false);
                                },
                                Entry::Filled{..} => {
                                    assert(pre.cache.status_map[old_slot] is Writeback);
                                    assert(false);
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                        }
                    }
                }
                assert(post.outstanding_cache_reqs.values() <= post.cache.lookup_map.dom());
                assert forall |id: ID| #[trigger] post.outstanding_cache_reqs.contains_key(id) implies {
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = post.cache.lookup_map[addr];
                    match post.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && post.cache.status_map[slot] is Writeback,
                        _ => false,
                    }
                } by {
                    let addr = post.outstanding_cache_reqs[id];
                    assert(pre.outstanding_cache_reqs.contains_key(id));
                    assert(pre.outstanding_cache_reqs[id] == addr);
                    let old_slot = pre.cache.lookup_map[addr];
                    assert(!evicted_addrs.contains(addr)) by {
                        if evicted_addrs.contains(addr) {
                            let evicted_map = Map::new(
                                |slot| evicted_slots.contains(slot),
                                |slot| pre.cache.entries[slot].get_addr(),
                            );
                            let evicted_slot = choose |slot: Slot|
                                evicted_map.contains_key(slot) && evicted_map[slot] == addr;
                            assert(evicted_slots.contains(evicted_slot));
                            assert(pre.cache.entries[evicted_slot].get_addr() == addr);
                            assert(pre.cache.lookup_map[addr] == evicted_slot);
                            assert(old_slot == evicted_slot);
                            assert(pre.cache.status_map[evicted_slot] is Clean);
                            assert(match pre.cache.entries[old_slot] {
                                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                                Entry::Filled{addr: entry_addr, ..} =>
                                    entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                                _ => false,
                            });
                            match pre.cache.entries[old_slot] {
                                Entry::Loading{..} => {
                                    assert(false);
                                },
                                Entry::Filled{..} => {
                                    assert(pre.cache.status_map[old_slot] is Writeback);
                                    assert(false);
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                        }
                    }
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == old_slot);
                    assert(!evicted_slots.contains(old_slot)) by {
                        if evicted_slots.contains(old_slot) {
                            assert(pre.cache.entries[old_slot] is Filled);
                            assert(pre.cache.status_map[old_slot] is Clean);
                            assert(match pre.cache.entries[old_slot] {
                                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                                Entry::Filled{addr: entry_addr, ..} =>
                                    entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                                _ => false,
                            });
                            match pre.cache.entries[old_slot] {
                                Entry::Loading{..} => {
                                    assert(false);
                                },
                                Entry::Filled{..} => {
                                    assert(pre.cache.status_map[old_slot] is Writeback);
                                    assert(false);
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                        }
                    }
                    assert(post.cache.entries[old_slot] == pre.cache.entries[old_slot]);
                    assert(post.cache.status_map[old_slot] == pre.cache.status_map[old_slot]);
                    assert(match pre.cache.entries[old_slot] {
                        Entry::Loading{addr: entry_addr} => entry_addr == addr,
                        Entry::Filled{addr: entry_addr, ..} =>
                            entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                        _ => false,
                    });
                }
            },
            Cache::Step::noop() => {
                assert(Cache::State::noop(pre.cache, post.cache, Cache::Label::Internal{}));
                assert(post.cache == pre.cache);
                Self::cache_request_wf_preserved_by_unchanged(pre, post);
            },
            Cache::Step::load_initiate(_) => {
                assert(Cache::State::load_initiate(pre.cache, post.cache, Cache::Label::Internal{}, arbitrary()));
                assert(false);
            },
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre.cache, post.cache, Cache::Label::Internal{}));
                assert(false);
            },
            Cache::Step::access() => {
                assert(Cache::State::access(pre.cache, post.cache, Cache::Label::Internal{}));
                assert(false);
            },
            Cache::Step::writeback_initiate() => {
                assert(Cache::State::writeback_initiate(pre.cache, post.cache, Cache::Label::Internal{}));
                assert(false);
            },
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(pre.cache, post.cache, Cache::Label::Internal{}));
                assert(false);
            },
            Cache::Step::evictable() => {
                assert(Cache::State::evictable(pre.cache, post.cache, Cache::Label::Internal{}));
                assert(false);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn cache_io_begin_preserves_cache_request_wf(
        pre: Self,
        post: Self,
        req_map: Map<ID, DiskRequest>,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    )
        requires
            pre.cache.inv(),
            pre.cache_request_wf(),
            Self::cache_io_begin(pre, post, req_map, reqs, resps),
        ensures
            post.cache_request_wf(),
    {
        let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
        let new_outstanding = pre.outstanding_cache_reqs.union_prefer_right(updated);
        let lbl = Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()};
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, lbl, step);
        assert(updated.is_injective());
        assert(!updated.contains_value(spec_superblock_addr()));
        assert forall |addr: Address| updated.values().contains(addr)
            implies !pre.outstanding_cache_reqs.values().contains(addr)
        by {
            let new_id = choose |id: ID| updated.contains_key(id) && updated[id] == addr;
            let req = req_map[new_id];
            assert(req.addr() == addr);
            if pre.outstanding_cache_reqs.values().contains(addr) {
                let old_id = choose |id: ID| pre.outstanding_cache_reqs.contains_key(id)
                    && pre.outstanding_cache_reqs[id] == addr;
                let old_slot = pre.cache.lookup_map[addr];
                assert(match pre.cache.entries[old_slot] {
                    Entry::Loading{addr: entry_addr} => entry_addr == addr,
                    Entry::Filled{addr: entry_addr, ..} =>
                        entry_addr == addr && pre.cache.status_map[old_slot] is Writeback,
                    _ => false,
                });
                match step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(pre.cache, post.cache, lbl, new_slots_mapping));
                        assert(req_map.values().contains(req));
                        assert(req is ReadReq);
                        assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                        assert(addr_maps_to_req(req_map.values(), req, addr));
                        assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                        assert(pre.cache.valid_new_slots_mapping(new_slots_mapping));
                        assert(new_slots_mapping.contains_value(addr));
                        assert(pre.cache.lookup_map.dom().contains(addr));
                        assert(new_slots_mapping.values().disjoint(pre.cache.lookup_map.dom()));
                        assert(false);
                    },
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(pre.cache, post.cache, lbl));
                        assert(req_map.values().contains(req));
                        assert(req is WriteReq);
                        assert(pre.cache.valid_writeback_requests(req_map.values()));
                        assert(pre.cache.lookup_map.contains_key(addr));
                        let slot = pre.cache.lookup_map[addr];
                        assert(pre.cache.entries[slot] == Entry::Filled{addr: addr, data: req->data});
                        assert(pre.cache.status_map[slot] is Dirty);
                        assert(slot == old_slot);
                        assert(false);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        }
        assert(new_outstanding.is_injective()) by {
            assert forall |id1: ID, id2: ID|
                id1 != id2
                && new_outstanding.contains_key(id1)
                && new_outstanding.contains_key(id2)
                implies #[trigger] new_outstanding[id1] != #[trigger] new_outstanding[id2]
            by {
                if updated.contains_key(id1) && updated.contains_key(id2) {
                    assert(updated[id1] != updated[id2]);
                    assert(new_outstanding[id1] == updated[id1]);
                    assert(new_outstanding[id2] == updated[id2]);
                } else if !updated.contains_key(id1) && !updated.contains_key(id2) {
                    assert(pre.outstanding_cache_reqs.contains_key(id1));
                    assert(pre.outstanding_cache_reqs.contains_key(id2));
                    assert(pre.outstanding_cache_reqs[id1] != pre.outstanding_cache_reqs[id2]);
                    assert(new_outstanding[id1] == pre.outstanding_cache_reqs[id1]);
                    assert(new_outstanding[id2] == pre.outstanding_cache_reqs[id2]);
                } else if updated.contains_key(id1) {
                    assert(pre.outstanding_cache_reqs.contains_key(id2));
                    assert(updated.values().contains(updated[id1]));
                    assert(!pre.outstanding_cache_reqs.values().contains(updated[id1]));
                    assert(new_outstanding[id1] == updated[id1]);
                    assert(new_outstanding[id2] == pre.outstanding_cache_reqs[id2]);
                } else {
                    assert(updated.contains_key(id2));
                    assert(pre.outstanding_cache_reqs.contains_key(id1));
                    assert(updated.values().contains(updated[id2]));
                    assert(!pre.outstanding_cache_reqs.values().contains(updated[id2]));
                    assert(new_outstanding[id1] == pre.outstanding_cache_reqs[id1]);
                    assert(new_outstanding[id2] == updated[id2]);
                }
            }
        }
        assert(!new_outstanding.contains_value(spec_superblock_addr())) by {
            if new_outstanding.contains_value(spec_superblock_addr()) {
                let id = choose |id: ID| new_outstanding.contains_key(id)
                    && new_outstanding[id] == spec_superblock_addr();
                if updated.contains_key(id) {
                    assert(updated.contains_value(spec_superblock_addr()));
                } else {
                    assert(pre.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
                }
                assert(false);
            }
        }
        assert forall |addr: Address| new_outstanding.values().contains(addr)
            implies post.cache.lookup_map.dom().contains(addr)
        by {
            let id = choose |id: ID| new_outstanding.contains_key(id) && new_outstanding[id] == addr;
            if updated.contains_key(id) {
                let req = req_map[id];
                assert(req.addr() == addr);
                match step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(pre.cache, post.cache, lbl, new_slots_mapping));
                        assert(req_map.values().contains(req));
                        assert(req is ReadReq);
                        assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                        assert(addr_maps_to_req(req_map.values(), req, addr));
                        assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                        assert(new_slots_mapping.contains_value(addr));
                        assert(post.cache.lookup_map.contains_key(addr));
                    },
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(pre.cache, post.cache, lbl));
                        assert(req_map.values().contains(req));
                        assert(req is WriteReq);
                        assert(pre.cache.valid_writeback_requests(req_map.values()));
                        assert(pre.cache.lookup_map.contains_key(addr));
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                    },
                    _ => {
                        assert(false);
                    },
                }
            } else {
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(pre.cache.lookup_map.dom().contains(addr));
                match step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(pre.cache, post.cache, lbl, new_slots_mapping));
                        assert(post.cache.lookup_map.contains_key(addr));
                    },
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(pre.cache, post.cache, lbl));
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        }
        assert(new_outstanding.values() <= post.cache.lookup_map.dom());
        assert forall |id: ID| #[trigger] new_outstanding.contains_key(id) implies {
            let addr = new_outstanding[id];
            let slot = post.cache.lookup_map[addr];
            match post.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && post.cache.status_map[slot] is Writeback,
                _ => false,
            }
        } by {
            let addr = new_outstanding[id];
            if updated.contains_key(id) {
                let req = req_map[id];
                assert(req.addr() == addr);
                match step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(pre.cache, post.cache, lbl, new_slots_mapping));
                        assert(req_map.values().contains(req));
                        assert(req is ReadReq);
                        assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                        assert(addr_maps_to_req(req_map.values(), req, addr));
                        assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                        assert(new_slots_mapping.contains_value(addr));
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let slot = new_slots_mapping.invert()[addr];
                        assert(new_slots_mapping.contains_pair(slot, addr));
                        assert(new_slots_mapping[slot] == addr);
                        assert(post.cache.lookup_map[addr] == slot);
                        let slot = post.cache.lookup_map[addr];
                        assert(post.cache.entries[slot] == Entry::Loading{addr});
                    },
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(pre.cache, post.cache, lbl));
                        assert(req_map.values().contains(req));
                        assert(req is WriteReq);
                        assert(pre.cache.valid_writeback_requests(req_map.values()));
                        let slot = pre.cache.lookup_map[addr];
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(pre.cache.entries[slot] == Entry::Filled{addr: addr, data: req->data});
                        let writeback_slots = Map::new(
                            |req: DiskRequest| req_map.values().contains(req),
                            |req: DiskRequest| pre.cache.lookup_map[req->to],
                        ).values();
                        let writeback_slot_map = Map::new(
                            |req: DiskRequest| req_map.values().contains(req),
                            |req: DiskRequest| pre.cache.lookup_map[req->to],
                        );
                        assert(writeback_slot_map.contains_key(req));
                        assert(writeback_slot_map[req] == slot);
                        assert(writeback_slots.contains(slot));
                        assert(post.cache.status_map[slot] is Writeback);
                    },
                    _ => {
                        assert(false);
                    },
                }
            } else {
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(pre.outstanding_cache_reqs[id] == addr);
                match step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(pre.cache, post.cache, lbl, new_slots_mapping));
                        assert(!updated.values().contains(addr));
                        assert(!new_slots_mapping.contains_value(addr)) by {
                            if new_slots_mapping.contains_value(addr) {
                                assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                                assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                                let r = choose |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr);
                                let new_id = choose |id: ID| req_map.contains_key(id) && req_map[id] == r;
                                assert(updated.contains_key(new_id));
                                assert(updated[new_id] == addr);
                                assert(updated.values().contains(addr));
                                assert(false);
                            }
                        }
                        let pre_slot = pre.cache.lookup_map[addr];
                        let post_slot = post.cache.lookup_map[addr];
                        assert(pre.outstanding_cache_reqs.values().contains(addr));
                        assert(pre.cache.lookup_map.contains_key(addr));
                        pre.cache.build_lookup_map_ensures();
                        assert(post_slot == pre_slot);
                        assert(!new_slots_mapping.contains_key(pre_slot)) by {
                            if new_slots_mapping.contains_key(pre_slot) {
                                assert(pre.cache.valid_new_slots_mapping(new_slots_mapping));
                                assert(pre.cache.entries[pre_slot] is Empty);
                                assert(match pre.cache.entries[pre_slot] {
                                    Entry::Loading{addr: entry_addr} => entry_addr == addr,
                                    Entry::Filled{addr: entry_addr, ..} =>
                                        entry_addr == addr && pre.cache.status_map[pre_slot] is Writeback,
                                    _ => false,
                                });
                                assert(false);
                            }
                        }
                        let updated_entries = Map::new(
                            |slot: Slot| new_slots_mapping.contains_key(slot),
                            |slot: Slot| Entry::Loading{addr: new_slots_mapping[slot]},
                        );
                        assert(!updated_entries.contains_key(pre_slot));
                        assert(!updated_entries.contains_key(post_slot));
                        assert(pre.cache.entries.contains_key(pre_slot));
                        assert(pre.cache.entries.contains_key(post_slot));
                        assert(post.cache.entries
                            == pre.cache.entries.union_prefer_right(updated_entries));
                        assert(post.cache.entries[post_slot]
                            == pre.cache.entries.union_prefer_right(updated_entries)[post_slot]);
                        assert(pre.cache.entries.union_prefer_right(updated_entries)[post_slot]
                            == pre.cache.entries[post_slot]);
                        assert(pre.cache.entries[post_slot] == pre.cache.entries[pre_slot]);
                        assert(post.cache.entries[post_slot] == pre.cache.entries[pre_slot]);
                        assert(post.cache.status_map[post_slot] == pre.cache.status_map[pre_slot]);
                    },
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(pre.cache, post.cache, lbl));
                        assert(!updated.values().contains(addr));
                        let pre_slot = pre.cache.lookup_map[addr];
                        let post_slot = post.cache.lookup_map[addr];
                        assert(pre.outstanding_cache_reqs.values().contains(addr));
                        assert(pre.cache.lookup_map.contains_key(addr));
                        pre.cache.build_lookup_map_ensures();
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post_slot == pre_slot);
                        assert(post.cache.entries[post_slot] == pre.cache.entries[pre_slot]);
                        let writeback_slots = Map::new(
                            |req: DiskRequest| req_map.values().contains(req),
                            |req: DiskRequest| pre.cache.lookup_map[req->to],
                        ).values();
                        assert(!writeback_slots.contains(pre_slot)) by {
                            if writeback_slots.contains(pre_slot) {
                                let r = choose |r: DiskRequest|
                                    req_map.values().contains(r) && pre.cache.lookup_map[r->to] == pre_slot;
                                let new_id = choose |id: ID| req_map.contains_key(id) && req_map[id] == r;
                                assert(updated.contains_key(new_id));
                                assert(r.addr() == r->to);
                                assert(pre.cache.lookup_map[r->to] == pre.cache.lookup_map[addr]);
                                assert(pre.cache.lookup_map.is_injective());
                                assert(r->to == addr);
                                assert(updated[new_id] == addr);
                                assert(updated.values().contains(addr));
                                assert(false);
                            }
                        }
                        let updated_status_map = Map::new(
                            |slot: Slot| writeback_slots.contains(slot),
                            |slot: Slot| Status::Writeback{},
                        );
                        assert(!updated_status_map.contains_key(pre_slot));
                        assert(!updated_status_map.contains_key(post_slot));
                        assert(pre.cache.status_map.contains_key(pre_slot));
                        assert(pre.cache.status_map.contains_key(post_slot));
                        assert(post.cache.status_map
                            == pre.cache.status_map.union_prefer_right(updated_status_map));
                        assert(post.cache.status_map[post_slot]
                            == pre.cache.status_map.union_prefer_right(updated_status_map)[post_slot]);
                        assert(pre.cache.status_map.union_prefer_right(updated_status_map)[post_slot]
                            == pre.cache.status_map[post_slot]);
                        assert(pre.cache.status_map[post_slot] == pre.cache.status_map[pre_slot]);
                        assert(post.cache.status_map[post_slot] == pre.cache.status_map[pre_slot]);
                    },
                    _ => {
                        assert(false);
                    },
                }
                let pre_slot = pre.cache.lookup_map[addr];
                let post_slot = post.cache.lookup_map[addr];
                assert(match pre.cache.entries[pre_slot] {
                    Entry::Loading{addr: entry_addr} => entry_addr == addr,
                    Entry::Filled{addr: entry_addr, ..} =>
                        entry_addr == addr && pre.cache.status_map[pre_slot] is Writeback,
                    _ => false,
                });
                assert(post_slot == pre_slot);
            }
        }
        assert(post.outstanding_cache_reqs == new_outstanding);
    }

    pub proof fn cache_io_end_preserves_cache_request_wf(
        pre: Self,
        post: Self,
        resp_map: Map<ID, DiskResponse>,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    )
        requires
            pre.cache.inv(),
            pre.cache_request_wf(),
            Self::cache_io_end(pre, post, resp_map, reqs, resps),
        ensures
            post.cache_request_wf(),
    {
        let new_outstanding = pre.outstanding_cache_reqs.remove_keys(resp_map.dom());
        let finished = pre.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
        let cache_resps = Map::new(
            |addr| finished.contains_key(addr),
            |addr| resp_map[finished[addr]],
        );
        let lbl = Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps};
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, lbl, step);
        assert(new_outstanding.is_injective());
        assert(!new_outstanding.contains_value(spec_superblock_addr()));
        assert forall |id: ID| #[trigger] new_outstanding.contains_key(id) implies {
            let addr = new_outstanding[id];
            let slot = post.cache.lookup_map[addr];
            match post.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && post.cache.status_map[slot] is Writeback,
                _ => false,
            }
        } by {
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(!resp_map.dom().contains(id));
            let addr = new_outstanding[id];
            assert(pre.outstanding_cache_reqs[id] == addr);
            assert(pre.outstanding_cache_reqs.values().contains(addr));
            assert(pre.cache.lookup_map.contains_key(addr));
            assert(!cache_resps.contains_key(addr)) by {
                if cache_resps.contains_key(addr) {
                    assert(finished.contains_key(addr));
                    let finished_id = finished[addr];
                    assert(pre.outstanding_cache_reqs.restrict(resp_map.dom()).contains_pair(finished_id, addr));
                    assert(pre.outstanding_cache_reqs.contains_key(finished_id));
                    assert(resp_map.dom().contains(finished_id));
                    assert(pre.outstanding_cache_reqs[finished_id] == addr);
                    assert(finished_id == id);
                    assert(false);
                }
            };
            let pre_slot = pre.cache.lookup_map[addr];
            pre.cache.build_lookup_map_ensures();
            assert(pre.cache.entries.contains_key(pre_slot));
            assert(pre.cache.status_map.contains_key(pre_slot));
            match step {
                Cache::Step::load_complete() => {
                    assert(Cache::State::load_complete(pre.cache, post.cache, lbl));
                    assert(post.cache.lookup_map == pre.cache.lookup_map);
                    let post_slot = post.cache.lookup_map[addr];
                    assert(post_slot == pre_slot);
                    let slot_addr_map = pre.cache.lookup_map.restrict(cache_resps.dom()).invert();
                    let updated_entries = Map::new(
                        |slot: Slot| slot_addr_map.contains_key(slot),
                        |slot: Slot| Entry::Filled{
                            addr: slot_addr_map[slot],
                            data: cache_resps[slot_addr_map[slot]]->data,
                        },
                    );
                    let updated_status_map = Map::new(
                        |slot: Slot| slot_addr_map.contains_key(slot),
                        |slot: Slot| Status::Clean,
                    );
                    assert(!slot_addr_map.contains_key(pre_slot)) by {
                        if slot_addr_map.contains_key(pre_slot) {
                            assert(pre.cache.lookup_map.restrict(cache_resps.dom()).contains_value(pre_slot));
                            let resp_addr = choose |a: Address|
                                pre.cache.lookup_map.restrict(cache_resps.dom()).contains_key(a)
                                && pre.cache.lookup_map.restrict(cache_resps.dom())[a] == pre_slot;
                            assert(cache_resps.contains_key(resp_addr));
                            assert(pre.cache.lookup_map[resp_addr] == pre.cache.lookup_map[addr]);
                            assert(pre.cache.lookup_map.is_injective());
                            assert(resp_addr == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_entries.contains_key(pre_slot));
                    assert(!updated_status_map.contains_key(pre_slot));
                    assert(post.cache.entries
                        == pre.cache.entries.union_prefer_right(updated_entries));
                    assert(post.cache.status_map
                        == pre.cache.status_map.union_prefer_right(updated_status_map));
                    assert(post.cache.entries[post_slot] == pre.cache.entries[pre_slot]);
                    assert(post.cache.status_map[post_slot] == pre.cache.status_map[pre_slot]);
                },
                Cache::Step::writeback_complete() => {
                    assert(Cache::State::writeback_complete(pre.cache, post.cache, lbl));
                    assert(post.cache.lookup_map == pre.cache.lookup_map);
                    assert(post.cache.entries == pre.cache.entries);
                    let post_slot = post.cache.lookup_map[addr];
                    assert(post_slot == pre_slot);
                    let resps_slots = pre.cache.lookup_map.restrict(cache_resps.dom()).values();
                    let updated_status_map = Map::new(
                        |slot: Slot| resps_slots.contains(slot),
                        |slot: Slot| Status::Clean,
                    );
                    assert(!resps_slots.contains(pre_slot)) by {
                        if resps_slots.contains(pre_slot) {
                            let resp_addr = choose |a: Address|
                                pre.cache.lookup_map.restrict(cache_resps.dom()).contains_key(a)
                                && pre.cache.lookup_map.restrict(cache_resps.dom())[a] == pre_slot;
                            assert(cache_resps.contains_key(resp_addr));
                            assert(pre.cache.lookup_map[resp_addr] == pre.cache.lookup_map[addr]);
                            assert(pre.cache.lookup_map.is_injective());
                            assert(resp_addr == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_status_map.contains_key(pre_slot));
                    assert(post.cache.status_map
                        == pre.cache.status_map.union_prefer_right(updated_status_map));
                    assert(post.cache.status_map[post_slot] == pre.cache.status_map[pre_slot]);
                },
                _ => {
                    assert(false);
                },
            }
            let post_slot = post.cache.lookup_map[addr];
            assert(match pre.cache.entries[pre_slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre.cache.status_map[pre_slot] is Writeback,
                _ => false,
            });
            assert(post_slot == pre_slot);
        }
        assert forall |addr: Address| new_outstanding.values().contains(addr)
            implies post.cache.lookup_map.dom().contains(addr)
        by {
            let id = choose |id: ID| new_outstanding.contains_key(id) && new_outstanding[id] == addr;
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(pre.outstanding_cache_reqs[id] == addr);
            assert(pre.cache.lookup_map.contains_key(addr));
            match step {
                Cache::Step::load_complete() => {
                    assert(Cache::State::load_complete(pre.cache, post.cache, lbl));
                    assert(post.cache.lookup_map == pre.cache.lookup_map);
                },
                Cache::Step::writeback_complete() => {
                    assert(Cache::State::writeback_complete(pre.cache, post.cache, lbl));
                    assert(post.cache.lookup_map == pre.cache.lookup_map);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(new_outstanding.values() <= post.cache.lookup_map.dom());
        assert(post.outstanding_cache_reqs == new_outstanding);
    }

    pub open spec fn initiate_recovery(
        pre: Self,
        post: Self,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
        req_id: ID,
    ) -> bool
    {
        &&& pre.recovery_state is Begin
        &&& reqs == Multiset::empty().insert((req_id, DiskRequest::ReadReq{from: spec_superblock_addr()}))
        &&& resps.is_empty()
        &&& post == Self{recovery_state: RecoveryState::AwaitingSuperblock, ..pre}
    }

    pub open spec fn superblock_recovery(
        pre: Self,
        post: Self,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
        req_id: ID,
        raw_page: RawPage,
        image: AbstractSuperblockImage,
    ) -> bool
    {
        let branch_image = AtomicBranchImage{
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        };
        &&& pre.recovery_state is AwaitingSuperblock
        &&& superblock_matches(raw_page, image)
        &&& AtomicBranchState::State::initialize(
            post.branch,
            branch_image,
            image.branch_roots.len() as nat,
        )
        &&& AtomicJournalState::State::initialize(
            post.journal,
            image.journal_snapshot,
            image.journal_seq_end,
        )
        &&& reqs.is_empty()
        &&& resps == Multiset::empty().insert((req_id, DiskResponse::ReadResp{data: raw_page}))
        &&& post == Self{
            recovery_state: RecoveryState::SuperblockAvailable,
            journal: post.journal,
            branch: post.branch,
            persistent_image: Some(image),
            in_flight: None,
            sync_req_map: Map::empty(),
            ..pre
        }
    }

    pub open spec fn recovery_complete(pre: Self, post: Self) -> bool
    {
        let end_lsn = pre.branch.seq_end();
        let journal_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};
        &&& pre.recovery_state is MetadataLoadComplete
        &&& AtomicJournalState::State::next(pre.journal, pre.journal, journal_lbl)
        &&& post == Self{
            recovery_state: RecoveryState::RecoveryComplete,
            ..pre
        }
    }

    pub proof fn recovery_complete_effect(pre: Self, post: Self)
        requires
            Self::recovery_complete(pre, post),
        ensures
            pre.recovery_state is MetadataLoadComplete,
            post.recovery_state is RecoveryComplete,
            post.cache == pre.cache,
            post.branch == pre.branch,
            post.journal == pre.journal,
            post.journal.journal == pre.journal.journal,
            post.journal.journal.seq_end() == pre.branch.seq_end(),
            post.journal.mini_allocator == pre.journal.mini_allocator,
            post.journal.in_flight == pre.journal.in_flight,
            post.journal.ready() == pre.journal.ready(),
            post.in_flight == pre.in_flight,
            post.branch.in_flight == pre.branch.in_flight,
    {
        let end_lsn = pre.branch.seq_end();
        let journal_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};
        assert(AtomicJournalState::State::next(pre.journal, pre.journal, journal_lbl));
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step: AtomicJournalState::Step|
            AtomicJournalState::State::next_by(pre.journal, pre.journal, journal_lbl, step);
        match step {
            AtomicJournalState::Step::query_end_lsn() => {
                assert(AtomicJournalState::State::query_end_lsn(
                    pre.journal,
                    pre.journal,
                    journal_lbl,
                )) by {
                    reveal(AtomicJournalState::State::query_end_lsn);
                }
                let cj_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
                assert(CachedJournal::State::next(
                    pre.journal.journal,
                    pre.journal.journal,
                    cj_lbl,
                ));
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let cj_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(
                        pre.journal.journal,
                        pre.journal.journal,
                        cj_lbl,
                        step,
                    );
                match cj_step {
                    CachedJournal::Step::query_end_lsn() => {
                        assert(CachedJournal::State::query_end_lsn(
                            pre.journal.journal,
                            pre.journal.journal,
                            cj_lbl,
                        )) by {
                            reveal(CachedJournal::State::query_end_lsn);
                        }
                    },
                    _ => {
                        assert(false);
                    },
                }
            },
            _ => {
                assert(false);
            },
        }
        assert(post == Self{
            recovery_state: RecoveryState::RecoveryComplete,
            ..pre
        });
    }

    pub proof fn recovery_complete_wf(pre: Self, post: Self)
        requires
            pre.wf(),
            Self::recovery_complete(pre, post),
        ensures
            post.wf(),
    {
        Self::recovery_complete_effect(pre, post);

        let end_lsn = pre.branch.seq_end();
        AtomicJournalState::State::wf_next(
            pre.journal,
            pre.journal,
            AtomicJournalState::Label::QueryEndLsn{end_lsn},
        );

        assert(post.journal.owned_aus() =~= pre.journal.owned_aus());
        assert(post.branch.owned_aus() =~= pre.branch.owned_aus());
        assert(post.component_owned_aus() =~= pre.component_owned_aus());
        assert(post.component_disjoint());
        assert(post.allocation_wf());

        assert(pre.recovery_metadata_wf());
        assert(pre.superblock_metadata_known());
        assert(pre.journal_metadata_loaded());
        assert(pre.branch_metadata_loaded());
        assert(post.superblock_metadata_known());
        assert(post.journal_metadata_loaded());
        assert(post.branch_metadata_loaded());
        assert(post.journal.journal.seq_end() == post.branch.seq_end());
        assert(post.recovery_metadata_wf());

        assert(post.in_flight_agrees());
        assert(post.wf());
    }

    pub open spec fn accept_sync_request(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        &&& !pre.sync_req_map.contains_key(sync_req_id)
        &&& post == Self{
            sync_req_map: pre.sync_req_map.insert(sync_req_id, pre.branch.seq_end()),
            ..pre
        }
    }

    pub open spec fn deliver_sync_reply(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        &&& pre.sync_req_map.contains_key(sync_req_id)
        &&& pre.sync_req_map[sync_req_id] <= pre.journal.persistent_seq_end
        &&& post == Self{
            sync_req_map: pre.sync_req_map.remove(sync_req_id),
            ..pre
        }
    }

    pub open spec fn execute_sync_begin(
        pre: Self,
        post: Self,
        req_id: ID,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
        image: AbstractSuperblockImage,
        journal_reads: Map<Address, RawPage>,
    ) -> bool
    {
        let inflight = AtomicInflightInfo{
            req_id,
            boundary_lsn: image.branch_seq_end,
        };
        let cache_lbl = Cache::Label::Access{reads: journal_reads, writes: Map::empty()};
        let journal_lbl = AtomicJournalState::Label::CommitStart{
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
            reads: to_journal_records(journal_reads),
        };
        let branch_lbl = AtomicBranchState::Label::CommitStart{
            branch_image: AtomicBranchImage{
                sealed_roots: image.branch_roots,
                seq_end: image.branch_seq_end,
            },
        };
        &&& pre.client_ready()
        &&& pre.in_flight is None
        &&& pre.sync_image_metadata_valid(image)
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& AtomicJournalState::State::next(pre.journal, post.journal, journal_lbl)
        &&& AtomicBranchState::State::next(pre.branch, post.branch, branch_lbl)
        &&& reqs.is_empty()
        &&& resps.is_empty()
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            branch: post.branch,
            in_flight: Some(inflight),
            ..pre
        }
    }

    pub open spec fn execute_sync_prepared(
        pre: Self,
        post: Self,
        req: DiskRequest,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) -> bool
    {
        let image = pre.atomic_inflight_superblock_i();
        &&& pre.client_ready()
        &&& pre.in_flight is Some
        &&& AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::CommitPrepared,
        )
        &&& AtomicBranchState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchState::Label::CommitPrepared,
        )
        &&& req is WriteReq
        &&& req->to == spec_superblock_addr()
        &&& req->data == marshal_abstract_superblock(image)
        &&& superblock_matches(req->data, image)
        &&& reqs == Multiset::singleton((pre.in_flight.unwrap().req_id, req))
        &&& resps.is_empty()
        &&& post == Self{
            journal: new_journal,
            branch: new_branch,
            ..pre
        }
    }

    pub open spec fn execute_sync_end(
        pre: Self,
        post: Self,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
        journal_discarded_aus: Set<AU>,
    ) -> bool
    {
        let image = pre.atomic_inflight_superblock_i();
        let branch_lbl = AtomicBranchState::Label::CommitComplete;
        let journal_lbl = AtomicJournalState::Label::CommitComplete{
            require_end: pre.journal.journal.seq_end(),
            discarded_aus: journal_discarded_aus,
        };
        &&& pre.client_ready()
        &&& pre.in_flight is Some
        &&& AtomicBranchState::State::next(pre.branch, post.branch, branch_lbl)
        &&& AtomicJournalState::State::next(pre.journal, post.journal, journal_lbl)
        &&& reqs.is_empty()
        &&& resps == Multiset::singleton((pre.in_flight.unwrap().req_id, DiskResponse::WriteResp{}))
        &&& post == Self{
            free_aus: pre.free_aus + journal_discarded_aus,
            journal: post.journal,
            branch: post.branch,
            persistent_image: Some(image),
            in_flight: None,
            ..pre
        }
    }

    pub open spec fn disk_transition(
        pre: Self,
        post: Self,
        disk_event: DiskEvent,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) -> bool
    {
        match disk_event {
            DiskEvent::InitiateRecovery{req_id} =>
                Self::initiate_recovery(pre, post, reqs, resps, req_id),
            DiskEvent::SuperblockRecovery{req_id, raw_page, image} =>
                Self::superblock_recovery(pre, post, reqs, resps, req_id, raw_page, image),
            DiskEvent::ExecuteSyncBegin{req_id, image, journal_reads} =>
                Self::execute_sync_begin(pre, post, req_id, reqs, resps, image, journal_reads),
            DiskEvent::ExecuteSyncPrepared{req} =>
                Self::execute_sync_prepared(pre, post, req, post.journal, post.branch, reqs, resps),
            DiskEvent::ExecuteSyncEnd{journal_discarded_aus} =>
                Self::execute_sync_end(pre, post, reqs, resps, journal_discarded_aus),
            DiskEvent::CacheIOBegin{req_map} =>
                Self::cache_io_begin(pre, post, req_map, reqs, resps),
            DiskEvent::CacheIOEnd{resp_map} =>
                Self::cache_io_end(pre, post, resp_map, reqs, resps),
        }
    }

    pub open spec fn internal_transition(pre: Self, post: Self, event: InternalEvent) -> bool
    {
        match event {
            InternalEvent::CacheInternal{} => Self::cache_internal(pre, post),
            InternalEvent::JournalLoadIndex{cache_reads, journal_reads, discovered_aus} =>
                Self::journal_load_index(pre, post, cache_reads, journal_reads, discovered_aus),
            InternalEvent::ReadForRecovery{
                addr,
                keys,
                msgs,
                receipt,
                init_root,
                journal_reads,
                branch_reads,
                writes,
                branch,
            } => Self::read_for_recovery(
                pre,
                post,
                addr,
                keys,
                msgs,
                receipt,
                init_root,
                journal_reads,
                branch_reads,
                writes,
                branch,
            ),
            InternalEvent::JournalMarshall{addr, raw_page} =>
                Self::journal_marshall(pre, post, addr, raw_page),
            InternalEvent::ObserveCleanJournalAUs{aus} =>
                Self::acknowledge_flushed_journal_aus(pre, post, aus),
            InternalEvent::JournalFillAUs{aus} => Self::journal_fill_aus(pre, post, aus),
            InternalEvent::BranchLoadMetadata{root, reads, discovered_aus} =>
                Self::branch_load_metadata(pre, post, root, reads, discovered_aus),
            InternalEvent::MetadataLoadComplete{} =>
                Self::metadata_load_complete(pre, post),
            InternalEvent::BranchGrow{new_root_addr, reads, writes, branch} =>
                Self::branch_grow(pre, post, new_root_addr, reads, writes, branch),
            InternalEvent::BranchSplit{new_child_addr, receipt, split_arg, reads, writes, branch} =>
                Self::branch_split(pre, post, new_child_addr, receipt, split_arg, reads, writes, branch),
            InternalEvent::BranchSeal{aux_ptr, summary, reads, writes, branch} =>
                Self::branch_seal(pre, post, aux_ptr, summary, reads, writes, branch),
            InternalEvent::BranchFillAUs{aus} => Self::branch_fill_aus(pre, post, aus),
            InternalEvent::ObservePersistedBranchRoots{target_count, aus} =>
                Self::observe_persisted_branch_roots(pre, post, target_count, aus),
            InternalEvent::RecoveryComplete{} => Self::recovery_complete(pre, post),
            InternalEvent::AcceptSyncRequest{sync_req_id} =>
                Self::accept_sync_request(pre, post, sync_req_id),
            InternalEvent::DeliverSyncReply{sync_req_id} =>
                Self::deliver_sync_reply(pre, post, sync_req_id),
        }
    }

    pub open spec fn journal_load_index_cached_next(
        pre: Self,
        post: Self,
        journal_reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
    ) -> bool
    {
        exists |step: CachedJournal::Step| CachedJournal::State::next_by(
            pre.journal.journal,
            post.journal.journal,
            CachedJournal::Label::LoadIndex{
                reads: to_journal_records(journal_reads),
                discovered_aus,
            },
            step,
        )
    }

    pub proof fn journal_load_index_effect(
        pre: Self,
        post: Self,
        cache_reads: Map<Address, RawPage>,
        journal_reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
    )
        requires
            Self::journal_load_index(pre, post, cache_reads, journal_reads, discovered_aus),
        ensures
            pre.recovery_state is SuperblockAvailable,
            journal_reads <= cache_reads,
            to_aus(journal_reads.dom()) <= discovered_aus,
            pre.journal.journal.status is None,
            post.journal.ready(),
            post.journal.loaded_index_aus() == discovered_aus,
            Cache::State::next(
                pre.cache,
                post.cache,
                Cache::Label::Access{reads: cache_reads, writes: Map::empty()},
            ),
            AtomicJournalState::State::next(
                pre.journal,
                post.journal,
                AtomicJournalState::Label::LoadIndex{
                    reads: to_journal_records(journal_reads),
                    discovered_aus,
                },
            ),
            exists |au_depth: nat, page_depth: nat| AtomicJournalState::State::load_index(
                pre.journal,
                post.journal,
                AtomicJournalState::Label::LoadIndex{
                    reads: to_journal_records(journal_reads),
                    discovered_aus,
                },
                post.journal.journal,
                au_depth,
                page_depth,
            ),
            CachedJournal::State::next(
                pre.journal.journal,
                post.journal.journal,
                CachedJournal::Label::LoadIndex{
                    reads: to_journal_records(journal_reads),
                    discovered_aus,
                },
            ),
            exists |step: CachedJournal::Step| CachedJournal::State::next_by(
                pre.journal.journal,
                post.journal.journal,
                CachedJournal::Label::LoadIndex{
                    reads: to_journal_records(journal_reads),
                    discovered_aus,
                },
                step,
            ),
            Self::journal_load_index_cached_next(pre, post, journal_reads, discovered_aus),
            post.journal.mini_allocator == pre.journal.mini_allocator,
            post.journal.persistent_seq_end == pre.journal.persistent_seq_end,
            post == (Self{
                cache: post.cache,
                free_aus: pre.free_aus - discovered_aus,
                journal: post.journal,
                ..pre
            }),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let lbl = AtomicJournalState::Label::LoadIndex{
            reads: to_journal_records(journal_reads),
            discovered_aus,
        };
        let step = choose |step: AtomicJournalState::Step|
            AtomicJournalState::State::next_by(pre.journal, post.journal, lbl, step);
        match step {
            AtomicJournalState::Step::load_index(new_journal, au_depth, page_depth) => {
                assert(AtomicJournalState::State::load_index(
                    pre.journal,
                    post.journal,
                    lbl,
                    new_journal,
                    au_depth,
                    page_depth,
                )) by {
                    reveal(AtomicJournalState::State::load_index);
                }
                assert(new_journal == post.journal.journal);
            },
            _ => {
                assert(false);
            },
        }
        reveal(CachedJournal::State::next);
        let cj_lbl = CachedJournal::Label::LoadIndex{
            reads: to_journal_records(journal_reads),
            discovered_aus,
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal.journal, post.journal.journal, cj_lbl, step);
        assert(CachedJournal::State::next_by(
            pre.journal.journal,
            post.journal.journal,
            cj_lbl,
            cj_step,
        ));
        CachedJournal::State::load_index_effect(
            pre.journal.journal,
            post.journal.journal,
            to_journal_records(journal_reads),
            discovered_aus,
        );
    }

    pub proof fn execute_put_journal_effect(
        pre: Self,
        post: Self,
        req: Request,
        reply: Reply,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    )
        requires
            Self::execute_put(pre, post, req, reply, receipt, init_root, reads, writes, branch),
        ensures
            ({
                let key = req.input.arrow_PutInput_key();
                let value = req.input.arrow_PutInput_value();
                let msg = Message::Define{value};
                let keyed_message = KeyedMessage{key, message: msg};
                let records = MsgHistory::singleton_at(pre.branch.seq_end(), keyed_message);
                AtomicJournalState::State::next(
                    pre.journal,
                    post.journal,
                    AtomicJournalState::Label::Put{messages: records},
                )
            }),
            ({
                let key = req.input.arrow_PutInput_key();
                let value = req.input.arrow_PutInput_value();
                let msg = Message::Define{value};
                let keyed_message = KeyedMessage{key, message: msg};
                let records = MsgHistory::singleton_at(pre.branch.seq_end(), keyed_message);
                CachedJournal::State::next(
                    pre.journal.journal,
                    post.journal.journal,
                    CachedJournal::Label::Put{messages: records},
                )
            }),
            pre.journal.ready(),
            post.journal.ready(),
            post.journal.mini_allocator == pre.journal.mini_allocator,
            post.journal.persistent_seq_end == pre.journal.persistent_seq_end,
            post.journal.in_flight == pre.journal.in_flight,
            post.journal.loaded_index_aus() =~= pre.journal.loaded_index_aus(),
            post == (Self{
                cache: post.cache,
                journal: post.journal,
                branch,
                ..pre
            }),
    {
        let key = req.input.arrow_PutInput_key();
        let value = req.input.arrow_PutInput_value();
        let msg = Message::Define{value};
        let keyed_message = KeyedMessage{key, message: msg};
        let records = MsgHistory::singleton_at(pre.branch.seq_end(), keyed_message);
        let lbl = AtomicJournalState::Label::Put{messages: records};
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step: AtomicJournalState::Step|
            AtomicJournalState::State::next_by(pre.journal, post.journal, lbl, step);
        match step {
            AtomicJournalState::Step::put(new_journal) => {
                assert(AtomicJournalState::State::put(pre.journal, post.journal, lbl, new_journal)) by {
                    reveal(AtomicJournalState::State::put);
                }
                assert(new_journal == post.journal.journal);
                assert(post.journal.in_flight == pre.journal.in_flight);
            },
            _ => {
                assert(false);
            },
        }
        let cj_lbl = CachedJournal::Label::Put{messages: records};
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal.journal, post.journal.journal, cj_lbl, step);
        match cj_step {
            CachedJournal::Step::put() => {
                assert(CachedJournal::State::put(pre.journal.journal, post.journal.journal, cj_lbl)) by {
                    reveal(CachedJournal::State::put);
                }
                assert(post.journal.journal.status is Some);
                assert(pre.journal.journal.status is Some);
                assert(post.journal.journal.status.unwrap().lsn_au_index
                    == pre.journal.journal.status.unwrap().lsn_au_index);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn read_for_recovery_journal_effect(
        pre: Self,
        post: Self,
        addr: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        journal_reads: Map<Address, RawPage>,
        branch_reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        branch: AtomicBranchState::State,
    )
        requires
            Self::read_for_recovery(
                pre,
                post,
                addr,
                keys,
                msgs,
                receipt,
                init_root,
                journal_reads,
                branch_reads,
                writes,
                branch,
            ),
        ensures
            ({
                let records = to_journal_records(journal_reads);
                let journal_records = records[addr].message_seq.maybe_discard_old(
                    pre.journal.journal.snapshot.boundary_lsn,
                );
                AtomicJournalState::State::next(
                    pre.journal,
                    post.journal,
                    AtomicJournalState::Label::ReadForRecovery{
                        messages: journal_records,
                        reads: records,
                    },
                )
            }),
            ({
                let records = to_journal_records(journal_reads);
                let journal_records = records[addr].message_seq.maybe_discard_old(
                    pre.journal.journal.snapshot.boundary_lsn,
                );
                CachedJournal::State::next(
                    pre.journal.journal,
                    post.journal.journal,
                    CachedJournal::Label::ReadForRecovery{
                        messages: journal_records,
                        reads: records,
                    },
                )
            }),
            post.journal == pre.journal,
            post == (Self{
                cache: post.cache,
                journal: post.journal,
                branch,
                ..pre
            }),
    {
        let records = to_journal_records(journal_reads);
        let journal_records = records[addr].message_seq.maybe_discard_old(
            pre.journal.journal.snapshot.boundary_lsn,
        );
        let lbl = AtomicJournalState::Label::ReadForRecovery{
            messages: journal_records,
            reads: records,
        };
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step: AtomicJournalState::Step|
            AtomicJournalState::State::next_by(pre.journal, post.journal, lbl, step);
        match step {
            AtomicJournalState::Step::read_for_recovery(new_journal) => {
                assert(AtomicJournalState::State::read_for_recovery(
                    pre.journal,
                    post.journal,
                    lbl,
                    new_journal,
                )) by {
                    reveal(AtomicJournalState::State::read_for_recovery);
                }
                assert(new_journal == post.journal.journal);
            },
            _ => {
                assert(false);
            },
        }
        let cj_lbl = CachedJournal::Label::ReadForRecovery{
            messages: journal_records,
            reads: records,
        };
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(pre.journal.journal, post.journal.journal, cj_lbl, step);
        match cj_step {
            CachedJournal::Step::read_for_recovery(start_lsn, read_addr) => {
                assert(CachedJournal::State::read_for_recovery(
                    pre.journal.journal,
                    post.journal.journal,
                    cj_lbl,
                    start_lsn,
                    read_addr,
                )) by {
                    reveal(CachedJournal::State::read_for_recovery);
                }
                assert(post.journal.journal == pre.journal.journal);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn execute_sync_end_journal_effect(
        pre: Self,
        post: Self,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
        journal_discarded_aus: Set<AU>,
    )
        requires
            Self::execute_sync_end(pre, post, reqs, resps, journal_discarded_aus),
        ensures
            pre.in_flight is Some,
            pre.journal.in_flight is Some,
            AtomicJournalState::State::next(
                pre.journal,
                post.journal,
                AtomicJournalState::Label::CommitComplete{
                    require_end: pre.journal.journal.seq_end(),
                    discarded_aus: journal_discarded_aus,
                },
            ),
            CachedJournal::State::next(
                pre.journal.journal,
                post.journal.journal,
                CachedJournal::Label::DiscardOld{
                    start_lsn: pre.journal.in_flight.unwrap().snapshot.boundary_lsn,
                    require_end: pre.journal.journal.seq_end(),
                    deallocs: journal_discarded_aus,
                },
            ),
            post.journal.persistent_seq_end == pre.journal.in_flight.unwrap().seq_end,
            post.journal.mini_allocator == pre.journal.mini_allocator.prune(journal_discarded_aus),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let lbl = AtomicJournalState::Label::CommitComplete{
            require_end: pre.journal.journal.seq_end(),
            discarded_aus: journal_discarded_aus,
        };
        let step = choose |step: AtomicJournalState::Step|
            AtomicJournalState::State::next_by(pre.journal, post.journal, lbl, step);
        match step {
            AtomicJournalState::Step::commit_complete(new_journal) => {
                assert(AtomicJournalState::State::commit_complete(
                    pre.journal,
                    post.journal,
                    lbl,
                    new_journal,
                )) by {
                    reveal(AtomicJournalState::State::commit_complete);
                }
                assert(new_journal == post.journal.journal);
            },
            _ => {
                assert(false);
            },
        }
    }
}

} // verus!
