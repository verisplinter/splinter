// ConcreteJournalRefinement: Proves that ConcreteJournal refines
// AbstractCrashAwareJournal via ConcreteJournal::State::i().
//
// For each ConcreteJournal transition, there's a corresponding ACAJ transition.
// Active transitions use the pattern:
//   1. JCS sub-state step → LikesJournal step (appeal to JournalCoordinationRefinement)
//   2. LikesJournal → LinkedJournal → PagedJournal → AbstractJournal (existing .i() chain)
//   3. AbstractJournal step + crash state → ACAJ step

#![allow(unused_imports)]
use vstd::prelude::*;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::ID;
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractCrashAwareJournal_v::{AbstractCrashAwareJournal, Ephemeral};
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::AtomicState_v::{InflightInfo, to_journal_reads};
use crate::allocation_layer::LikesJournal_v::{LikesJournal, LsnAddrIndex};
use crate::implementation::JournalCoordinationSystem_v::*;
use crate::implementation::ConcreteJournal_v::ConcreteJournal;

verus!{

impl ConcreteJournal::State {
    /// Map a ConcreteJournal label to the corresponding ACAJ label
    pub open spec fn i_lbl(pre: Self, post: Self, lbl: ConcreteJournal::Label) -> AbstractCrashAwareJournal::Label
    {
        match lbl {
            ConcreteJournal::Label::LoadEphemeral{} =>
                AbstractCrashAwareJournal::Label::LoadEphemeralFromPersistentLabel,
            ConcreteJournal::Label::ReadForRecovery{messages} =>
                AbstractCrashAwareJournal::Label::ReadForRecoveryLabel{records: messages},
            ConcreteJournal::Label::QueryEndLsn{end_lsn} =>
                AbstractCrashAwareJournal::Label::QueryEndLsnLabel{end_lsn},
            ConcreteJournal::Label::Put{messages} =>
                AbstractCrashAwareJournal::Label::PutLabel{records: messages},
            ConcreteJournal::Label::Internal{} =>
                AbstractCrashAwareJournal::Label::InternalLabel,
            ConcreteJournal::Label::QueryLsnPersistence{sync_lsn} =>
                AbstractCrashAwareJournal::Label::QueryLsnPersistenceLabel{sync_lsn},
            ConcreteJournal::Label::CommitStart{new_boundary_lsn, max_lsn} =>
                AbstractCrashAwareJournal::Label::CommitStartLabel{new_boundary_lsn, max_lsn},
            ConcreteJournal::Label::CommitComplete{require_end} =>
                AbstractCrashAwareJournal::Label::CommitCompleteLabel{require_end},
            ConcreteJournal::Label::Crash{keep_in_flight} =>
                AbstractCrashAwareJournal::Label::CrashLabel{keep_in_flight},
        }
    }

    // ================================================================
    // Per-transition refinement lemmas
    // ================================================================

    proof fn read_for_recovery_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label, reads: Map<Address, RawPage>)
        requires
            pre.inv(),
            ConcreteJournal::State::read_for_recovery(pre, post, lbl, reads),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        // pre.i() == post.i() since read_for_recovery doesn't change state
        // The ACAJ read_for_recovery requires ephemeral is Known and AJ step
        assume(false); // TODO: needs JCS refinement chain reasoning
    }

    proof fn query_end_lsn_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label)
        requires
            pre.inv(),
            ConcreteJournal::State::query_end_lsn(pre, post, lbl),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO
    }

    proof fn put_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label, new_journal: CachedJournal::State)
        requires
            pre.inv(),
            ConcreteJournal::State::put(pre, post, lbl, new_journal),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO: Put extends journal
    }

    proof fn internal_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label)
        requires
            pre.inv(),
            ConcreteJournal::State::internal_journal(pre, post, lbl),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        // internal_journal is a no-op on concrete state → i() unchanged
        // ACAJ internal requires AJ::next which is also a no-op
        assume(false); // TODO
    }

    proof fn internal_marshal_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label,
        new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord)
        requires
            pre.inv(),
            ConcreteJournal::State::internal_journal_marshal(pre, post, lbl, new_journal, new_cache, addr, record),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        // Journal marshal changes marshalled/unmarshalled split but not full_journal
        assume(false); // TODO
    }

    proof fn internal_cache_disk_ops_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label,
        new_cache: Cache::State, new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>)
        requires
            pre.inv(),
            ConcreteJournal::State::internal_cache_disk_ops(pre, post, lbl, new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        // Cache/disk ops don't change the abstract journal
        assume(false); // TODO
    }

    proof fn internal_cache_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label, new_cache: Cache::State)
        requires
            pre.inv(),
            ConcreteJournal::State::internal_cache(pre, post, lbl, new_cache),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO
    }

    proof fn internal_disk_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label, new_disk: AsyncDisk::State)
        requires
            pre.inv(),
            ConcreteJournal::State::internal_disk(pre, post, lbl, new_disk),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO
    }

    proof fn query_lsn_persistence_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label)
        requires
            pre.inv(),
            ConcreteJournal::State::query_lsn_persistence(pre, post, lbl),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        // sync_lsn <= persistent_journal_seq_end, and
        // pre.i().persistent = full_journal.discard_recent(persistent_journal_seq_end)
        // so sync_lsn <= pre.i().persistent.seq_end
        assume(false); // TODO
    }

    proof fn commit_start_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label,
        frozen: JournalSnapshot, frozen_domain: Set<Address>, reads: Map<Address, RawPage>)
        requires
            pre.inv(),
            ConcreteJournal::State::commit_start(pre, post, lbl, frozen, frozen_domain, reads),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO: needs freeze reasoning
    }

    proof fn commit_complete_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label,
        new_journal: CachedJournal::State, discard_addrs: Set<Address>)
        requires
            pre.inv(),
            ConcreteJournal::State::commit_complete(pre, post, lbl, new_journal, discard_addrs),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO: needs discard_old reasoning
    }

    proof fn crash_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label)
        requires
            pre.inv(),
            ConcreteJournal::State::crash(pre, post, lbl),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO
    }

    proof fn load_ephemeral_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label,
        new_journal: CachedJournal::State)
        requires
            pre.inv(),
            ConcreteJournal::State::load_ephemeral(pre, post, lbl, new_journal),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(AbstractCrashAwareJournal::State::next);
        reveal(AbstractCrashAwareJournal::State::next_by);
        assume(false); // TODO
    }

    /// Master refinement lemma: any ConcreteJournal next step has a corresponding ACAJ step.
    proof fn next_refines(pre: Self, post: Self, lbl: ConcreteJournal::Label)
        requires
            pre.inv(),
            post.inv(),
            ConcreteJournal::State::next(pre, post, lbl),
        ensures
            AbstractCrashAwareJournal::State::next(pre.i(), post.i(), Self::i_lbl(pre, post, lbl)),
    {
        reveal(ConcreteJournal::State::next);
        reveal(ConcreteJournal::State::next_by);

        let step = choose |step| ConcreteJournal::State::next_by(pre, post, lbl, step);
        match step {
            ConcreteJournal::Step::read_for_recovery(reads) =>
                Self::read_for_recovery_refines(pre, post, lbl, reads),
            ConcreteJournal::Step::query_end_lsn() =>
                Self::query_end_lsn_refines(pre, post, lbl),
            ConcreteJournal::Step::put(new_journal) =>
                Self::put_refines(pre, post, lbl, new_journal),
            ConcreteJournal::Step::internal_journal() =>
                Self::internal_refines(pre, post, lbl),
            ConcreteJournal::Step::internal_journal_marshal(new_journal, new_cache, addr, record) =>
                Self::internal_marshal_refines(pre, post, lbl, new_journal, new_cache, addr, record),
            ConcreteJournal::Step::internal_cache_disk_ops(new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses) =>
                Self::internal_cache_disk_ops_refines(pre, post, lbl, new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses),
            ConcreteJournal::Step::internal_cache(new_cache) =>
                Self::internal_cache_refines(pre, post, lbl, new_cache),
            ConcreteJournal::Step::internal_disk(new_disk) =>
                Self::internal_disk_refines(pre, post, lbl, new_disk),
            ConcreteJournal::Step::query_lsn_persistence() =>
                Self::query_lsn_persistence_refines(pre, post, lbl),
            ConcreteJournal::Step::commit_start(frozen, frozen_domain, reads) =>
                Self::commit_start_refines(pre, post, lbl, frozen, frozen_domain, reads),
            ConcreteJournal::Step::commit_complete(new_journal, discard_addrs) =>
                Self::commit_complete_refines(pre, post, lbl, new_journal, discard_addrs),
            ConcreteJournal::Step::crash() =>
                Self::crash_refines(pre, post, lbl),
            ConcreteJournal::Step::load_ephemeral(new_journal) =>
                Self::load_ephemeral_refines(pre, post, lbl, new_journal),
            _ => { }  // dummy_to_use_type_params
        }
    }
}

}
