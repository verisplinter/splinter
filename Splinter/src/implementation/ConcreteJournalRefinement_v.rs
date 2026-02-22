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
use vstd::map::*;

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
use crate::journal::PagedJournal_v;
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
    // Helper: full_journal().wf() from CJ invariant
    // ================================================================

    proof fn full_journal_wf(pre: Self)
        requires
            pre.inv(),
            pre.journal.status is Some,
        ensures
            pre.full_journal().wf(),
            pre.i().ephemeral->v.wf(),
    {
        let jcs = pre.jcs_view();
        let tj = jcs.ephemeral_tj();
        let tail = cj_unmarshalled_tail(pre.journal);

        // From CJ invariant: valid_journal_structure gives decodable + seq alignment
        assert(jcs.valid_journal_structure());
        assert(tj.decodable()); // = wf() && acyclic()

        // tail.wf() from journal_seq_end_inv: tail.can_discard_to(pjse) → seq_start <= seq_end
        assert(pre.journal_seq_end_inv());
        assert(tail.can_discard_to(pre.persistent_journal_seq_end));

        // LinkedJournal wf: all four conditions met
        let lj = jcs.i().journal;
        assert(lj.truncated_journal == tj);
        assert(lj.unmarshalled_tail == tail);
        assert(lj.wf());
        assert(lj.truncated_journal.disk_view.acyclic());

        // Step 1: iwf(): LinkedJournal wf + acyclic → PagedJournal wf
        lj.iwf();
        let pj = lj.i();
        assert(pj.wf());

        // Step 2: PagedJournal TruncatedJournal.i() wf via JournalRecord::i_lemma_forall
        PagedJournal_v::JournalRecord::i_lemma_forall();

        // Step 3: concat(wf TJ interpretation, wf tail) with matching seq → wf
        // pj.i().journal = pj.truncated_journal.i().concat(pj.unmarshalled_tail)
        // After i_lemma_forall: pj.truncated_journal.i().wf() with correct bounds
        // pj.wf() gives: pj.truncated_journal.seq_end() == pj.unmarshalled_tail.seq_start
        // So concat result wf follows from transitivity of <=
    }

    /// full_journal().seq_end == unmarshalled_tail.seq_end
    /// Follows from the concat chain: full_journal = TJ.i().concat(tail), and
    /// concat(a,b).seq_end = b.seq_end by definition.
    proof fn full_journal_seq_end(pre: Self)
        requires
            pre.inv(),
            pre.journal.status is Some,
        ensures
            pre.full_journal().seq_end == cj_unmarshalled_tail(pre.journal).seq_end,
    {
        let jcs = pre.jcs_view();
        let tj = jcs.ephemeral_tj();
        let tail = cj_unmarshalled_tail(pre.journal);
        assert(jcs.valid_journal_structure());
        assert(tj.decodable());

        // LinkedJournal.i() preserves unmarshalled_tail
        let lj = jcs.i().journal;
        assert(lj.truncated_journal == tj);
        assert(lj.unmarshalled_tail == tail);
        assert(lj.wf());
        assert(lj.truncated_journal.disk_view.acyclic());
        let pj = lj.i();
        assert(pj.unmarshalled_tail == tail);

        // PagedJournal.i().journal = pj.truncated_journal.i().concat(tail)
        // concat(a, b).seq_end = b.seq_end by definition of MsgHistory::concat
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // read_for_recovery doesn't change state: post == pre
        // ACAJ read_for_recovery requires: AJ::next(ephemeral.v, ephemeral.v, ReadForRecoveryLabel{messages})
        // AJ read_for_recovery requires: pre.wf() and pre.journal.includes_subseq(messages)
        let aj = pre.i().ephemeral->v;
        let messages = lbl.arrow_ReadForRecovery_messages();
        Self::full_journal_wf(pre);
        assert(aj.journal.includes_subseq(messages));
        let aj_lbl = AbstractJournal::Label::ReadForRecoveryLabel{messages};
        assert(AbstractJournal::State::next_by(aj, aj, aj_lbl, AbstractJournal::Step::read_for_recovery()));
        assert(AbstractJournal::State::next(aj, aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(pre.i() == post.i());
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::read_for_recovery()));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // query_end_lsn doesn't change state: post == pre
        // CJ requires: end_lsn == journal.seq_end() == unmarshalled_tail.seq_end
        // ACAJ requires: AJ::next(ephemeral.v, ephemeral.v, QueryEndLsnLabel{end_lsn})
        // AJ observe_fresh_journal requires: pre.wf() and pre.can_end_at(end_lsn)
        // i.e. full_journal().seq_end == end_lsn
        let aj = pre.i().ephemeral->v;
        let end_lsn = lbl->end_lsn;
        Self::full_journal_wf(pre);
        // Reveal CachedJournal transition to see end_lsn == seq_end() == unmarshalled_tail.seq_end
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        Self::full_journal_seq_end(pre);
        assert(aj.can_end_at(end_lsn));
        let aj_lbl = AbstractJournal::Label::QueryEndLsnLabel{end_lsn};
        assert(AbstractJournal::State::next_by(aj, aj, aj_lbl, AbstractJournal::Step::observe_fresh_journal()));
        assert(AbstractJournal::State::next(aj, aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(pre.i() == post.i());
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::query_end_lsn()));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        reveal(ConcreteJournal::State::commit_complete);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let messages = lbl.arrow_Put_messages();
        let pre_aj = pre.i().ephemeral->v;
        let post_aj = AbstractJournal::State{ journal: pre_aj.journal.concat(messages) };

        Self::full_journal_wf(pre);
        Self::full_journal_seq_end(pre);
        // From CachedJournal put: messages.wf() and messages.seq_start == pre.seq_end()
        assert(messages.wf());
        assert(pre_aj.journal.seq_end == messages.seq_start);

        // Trace the interpretation chain.
        // CJ put only changes journal.unmarshalled_tail; cache, disk, pjse, in_flight unchanged.
        let jcs_pre = pre.jcs_view();
        let jcs_post = post.jcs_view();

        // ephemeral_disk/ephemeral_tj unchanged (cache, disk, snapshot, lsn_addr_index same)
        let old_tail = cj_unmarshalled_tail(pre.journal);
        let new_tail = cj_unmarshalled_tail(post.journal);
        assert(new_tail == old_tail.concat(messages));

        // Build LinkedJournal interpretation for pre
        let lj_pre = jcs_pre.i().journal;
        assert(jcs_pre.valid_journal_structure());
        assert(jcs_pre.ephemeral_tj().decodable());
        assert(lj_pre.truncated_journal == jcs_pre.ephemeral_tj());
        assert(lj_pre.unmarshalled_tail == old_tail);
        assert(lj_pre.wf());
        assert(lj_pre.truncated_journal.disk_view.acyclic());

        // Build LinkedJournal interpretation for post
        let lj_post = jcs_post.i().journal;
        assert(lj_post.truncated_journal == jcs_pre.ephemeral_tj());
        assert(lj_post.unmarshalled_tail == new_tail);

        // PagedJournal level: truncated_journal.i() is the same for pre and post
        let pj_pre = lj_pre.i();
        let pj_post = lj_post.i();
        assert(pj_pre.truncated_journal == pj_post.truncated_journal);
        let tj_decoded = pj_pre.truncated_journal.i();

        // Concat associativity: TJ.i().concat(old_tail.concat(messages))
        //   == TJ.i().concat(old_tail).concat(messages)
        // (Same approach as PagedJournalRefinement_v.rs line 511)
        assert_maps_equal!(
            tj_decoded.concat(old_tail.concat(messages)).msgs,
            tj_decoded.concat(old_tail).concat(messages).msgs
        );
        // Now: post.full_journal() == pre.full_journal().concat(messages)
        assert(post.i().ephemeral == Ephemeral::Known{ v: post_aj });

        // Persistent stability: discard_recent(pjse) absorbs trailing concat.
        // messages.wf() → msgs keys are in [messages.seq_start, messages.seq_end),
        // and messages.seq_start == pre.full_journal().seq_end >= pjse,
        // so for k < pjse, !messages.msgs.contains_key(k).
        let h = pre.full_journal();
        let pjse = pre.persistent_journal_seq_end;
        assert_maps_equal!(
            h.concat(messages).discard_recent(pjse).msgs,
            h.discard_recent(pjse).msgs
        );
        assert(post.i().persistent == pre.i().persistent);

        // In-flight stability: same argument at in_flight LSN
        if pre.in_flight is Some {
            let ifl = pre.in_flight.unwrap().journal_version;
            let bdy = pre.in_flight.unwrap().new_boundary_lsn;
            assert_maps_equal!(
                h.concat(messages).discard_recent(ifl).msgs,
                h.discard_recent(ifl).msgs
            );
            assert_maps_equal!(
                h.concat(messages).discard_recent(ifl).discard_old(bdy).msgs,
                h.discard_recent(ifl).discard_old(bdy).msgs
            );
        }
        assert(post.i().in_flight == pre.i().in_flight);

        let aj_lbl = AbstractJournal::Label::PutLabel{messages};
        assert(AbstractJournal::State::next_by(pre_aj, post_aj, aj_lbl, AbstractJournal::Step::put()));
        assert(AbstractJournal::State::next(pre_aj, post_aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::put(post_aj)));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // internal_journal is a complete no-op: post == pre, so post.i() == pre.i()
        // ephemeral is Known. ACAJ internal step: requires AJ::next(v, v, InternalLabel)
        // AJ internal is a no-op requiring only pre.wf() (= full_journal().wf())
        let aj = pre.i().ephemeral->v;
        Self::full_journal_wf(pre);

        // Break down: first prove AJ step, then ACAJ step
        let aj_lbl = AbstractJournal::Label::InternalLabel;
        assert(AbstractJournal::State::next_by(aj, aj, aj_lbl, AbstractJournal::Step::internal()));
        assert(AbstractJournal::State::next(aj, aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(pre.i() == post.i());
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::internal(aj)));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // Journal marshal moves data from unmarshalled_tail to on-disk via cache.
        // full_journal() (on-disk decoded ++ tail) should be unchanged.
        // Note: internal_journal_marshal requires pre.journal.status is Some.
        let aj = pre.i().ephemeral->v;
        reveal(ConcreteJournal::State::internal_journal_marshal);
        assert(pre.full_journal() == post.full_journal());
        Self::full_journal_wf(pre);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: Map::empty().insert(addr, record)};
        let journal_step = choose |step| CachedJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
        match journal_step {
            CachedJournal::Step::internal_journal_marshal(cut, marshalled_addr) => {
                assert(new_journal.status is Some);
            }
            _ => { assert(false); }
        }
        assert(post.journal == new_journal);
        assert(post.journal.status is Some);
        let post_aj = post.i().ephemeral->v;
        assert(aj == post_aj);
        let aj_lbl = AbstractJournal::Label::InternalLabel;
        assert(AbstractJournal::State::next_by(aj, post_aj, aj_lbl, AbstractJournal::Step::internal()));
        assert(AbstractJournal::State::next(aj, post_aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(post.i().ephemeral is Known);
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::internal(post_aj)));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // Cache/disk I/O: dirty pages flush to disk, reads load from disk.
        // ephemeral_disk = persistent_journal_disk ∪ dirty_journal_cache.
        // I/O moves pages between cache and disk but preserves ephemeral_disk,
        // so full_journal() is unchanged.
        let aj = pre.i().ephemeral->v;
        Self::full_journal_wf(pre);
        reveal(ConcreteJournal::State::internal_cache_disk_ops);
        assert(pre.full_journal() == post.full_journal());
        let aj_lbl = AbstractJournal::Label::InternalLabel;
        assert(AbstractJournal::State::next_by(aj, aj, aj_lbl, AbstractJournal::Step::internal()));
        assert(AbstractJournal::State::next(aj, aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::internal(aj)));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // Cache internal step (eviction, etc.) — journal and disk unchanged.
        // full_journal() depends on dirty_journal_cache which depends on cache,
        // so we need to show the internal step preserves it.
        let aj = pre.i().ephemeral->v;
        Self::full_journal_wf(pre);
        reveal(ConcreteJournal::State::internal_cache);
        assert(pre.full_journal() == post.full_journal());
        let aj_lbl = AbstractJournal::Label::InternalLabel;
        assert(AbstractJournal::State::next_by(aj, aj, aj_lbl, AbstractJournal::Step::internal()));
        assert(AbstractJournal::State::next(aj, aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::internal(aj)));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        // Disk internal step — journal and cache unchanged.
        // full_journal() depends on persistent_journal_disk which depends on disk.content.
        let aj = pre.i().ephemeral->v;
        Self::full_journal_wf(pre);
        reveal(ConcreteJournal::State::internal_disk);
        assert(pre.full_journal() == post.full_journal());
        let aj_lbl = AbstractJournal::Label::InternalLabel;
        assert(AbstractJournal::State::next_by(aj, aj, aj_lbl, AbstractJournal::Step::internal()));
        assert(AbstractJournal::State::next(aj, aj, aj_lbl));
        assert(pre.i().ephemeral is Known);
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::internal(aj)));
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
        // query_lsn_persistence doesn't change state: post == pre
        // CJ requires: sync_lsn <= persistent_journal_seq_end
        // pre.i().persistent = full_journal().discard_recent(persistent_journal_seq_end)
        // discard_recent(lsn).seq_end == lsn, so pre.i().persistent.seq_end == persistent_journal_seq_end
        // ACAJ query_lsn_persistence just requires: sync_lsn <= pre.persistent.seq_end
        assert(AbstractCrashAwareJournal::State::next_by(pre.i(), post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::query_lsn_persistence()));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);

        let pre_aj = pre.i().ephemeral->v;
        let frozen_journal = post.i().in_flight.unwrap();
        Self::full_journal_wf(pre);

        // commit_start keeps concrete journal/cache/disk unchanged, so AJ view is unchanged.
        assert(pre.full_journal() == post.full_journal());
        assert(pre.i().ephemeral == post.i().ephemeral);
        assert(pre.i().persistent == post.i().persistent);
        assert(pre.i().in_flight is None);

        assert(post.in_flight is Some);
        let ifl = post.in_flight.unwrap();
        Self::full_journal_seq_end(pre);
        assert(ifl.new_boundary_lsn == lbl->new_boundary_lsn);
        assert(ifl.journal_version == frozen_journal.seq_end);
        assert(frozen_journal.seq_start == ifl.new_boundary_lsn);
        assert(ifl.journal_version <= lbl->max_lsn);
        assert(lbl->max_lsn == pre.full_journal().seq_end);
        assert(ifl.journal_version <= pre.full_journal().seq_end);
        assert(pre.full_journal().can_discard_to(ifl.journal_version));
        assert(pre.full_journal().discard_recent(ifl.journal_version).can_discard_to(ifl.new_boundary_lsn));
        assert(frozen_journal
            == pre.full_journal().discard_recent(ifl.journal_version).discard_old(ifl.new_boundary_lsn));
        assert(frozen_journal.wf());
        assert(pre.i().persistent.seq_end == pre.persistent_journal_seq_end);
        assert(pre.i().persistent.seq_end <= ifl.journal_version);
        assert(pre.i().persistent.seq_end <= frozen_journal.seq_end);
        assert(pre_aj.journal.includes_subseq(frozen_journal));
        assert(AbstractJournal::State::next_by(
            pre_aj,
            pre_aj,
            AbstractJournal::Label::FreezeForCommitLabel{frozen_journal},
            AbstractJournal::Step::freeze_for_commit(),
        ));
        assert(AbstractJournal::State::next(
            pre_aj,
            pre_aj,
            AbstractJournal::Label::FreezeForCommitLabel{frozen_journal},
        ));
        assert(lbl->new_boundary_lsn <= lbl->max_lsn);
        assert(pre.i().ephemeral is Known);
        assert(post.i().in_flight is Some);
        assert(AbstractCrashAwareJournal::State::next_by(
            pre.i(),
            post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::commit_start(frozen_journal),
        ));
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
        reveal(AbstractJournal::State::next);
        reveal(AbstractJournal::State::next_by);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);

        let pre_aj = pre.i().ephemeral->v;
        let start_lsn = pre.i().in_flight.unwrap().seq_start;

        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn: pre.in_flight.unwrap().new_boundary_lsn,
            require_end: lbl->require_end,
            discard_addrs,
        };
        let journal_step = choose |step| CachedJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
        match journal_step {
            CachedJournal::Step::discard_old() => {
                assert(new_journal.status is Some);
            }
            _ => { assert(false); }
        }
        assert(post.journal == new_journal);
        assert(post.journal.status is Some);
        let post_aj = post.i().ephemeral->v;

        // Remaining obligations from relating ConcreteJournal discard to AJ discard_old.
        Self::full_journal_wf(pre);
        assert(pre_aj.wf());
        assert(pre_aj.can_end_at(lbl->require_end));
        assert(pre_aj.journal.can_discard_to(start_lsn));
        assert(post_aj.journal == pre_aj.journal.discard_old(start_lsn));
        assert(AbstractJournal::State::next_by(
            pre_aj,
            post_aj,
            AbstractJournal::Label::DiscardOldLabel{start_lsn, require_end: lbl->require_end},
            AbstractJournal::Step::discard_old(),
        ));
        assert(AbstractJournal::State::next(
            pre_aj,
            post_aj,
            AbstractJournal::Label::DiscardOldLabel{start_lsn, require_end: lbl->require_end},
        ));
        assert(post_aj.journal == pre_aj.journal.discard_old(start_lsn));
        assert(post.persistent_journal_seq_end == pre.in_flight.unwrap().journal_version);
        let jv = pre.in_flight.unwrap().journal_version;
        let bdy = pre.in_flight.unwrap().new_boundary_lsn;
        assert(start_lsn == bdy);
        let left = pre_aj.journal.discard_old(start_lsn).discard_recent(jv);
        let right = pre_aj.journal.discard_recent(jv).discard_old(start_lsn);
        assert(left.ext_equal(right));
        MsgHistory::ext_equal_is_equality();
        assert(left == right);
        assert(post.i().persistent == pre.i().in_flight.unwrap());
        assert(pre.i().ephemeral is Known);
        assert(post.i().ephemeral is Known);
        assert(post.i().in_flight is None);
        assert(AbstractCrashAwareJournal::State::next_by(
            pre.i(),
            post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::commit_complete(post_aj),
        ));
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
        assert(post.journal.status is None);
        assert(post.i().ephemeral is Unknown);
        assert(post.i().in_flight is None);
        if pre.journal.status is Some {
            assert(pre.persistent_image == pre.i().persistent);
            if lbl->keep_in_flight && pre.in_flight is Some {
                assert(post.persistent_image
                    == pre.full_journal()
                        .discard_recent(pre.in_flight.unwrap().journal_version)
                        .discard_old(pre.in_flight.unwrap().new_boundary_lsn));
                assert(pre.i().in_flight is Some);
                assert(post.i().persistent == pre.i().in_flight.unwrap());
            } else {
                assert(post.persistent_image == pre.persistent_image);
                assert(post.i().persistent == pre.i().persistent);
            }
        } else {
            assert(pre.i().in_flight is None);
            assert(post.persistent_image == pre.persistent_image);
            assert(post.i().persistent == pre.i().persistent);
        }
        assert(AbstractCrashAwareJournal::State::next_by(
            pre.i(),
            post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::crash(),
        ));
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
        reveal(AbstractJournal::State::init_by);
        assert(pre.journal.status is None);
        assert(pre.in_flight is None);
        assert(pre.i().ephemeral is Unknown);
        assert(post.in_flight == pre.in_flight);
        assert(post.i().in_flight == pre.i().in_flight);
        assert(post.journal.status is Some);
        let post_aj = post.i().ephemeral->v;
        assert(post.i().persistent == pre.i().persistent);
        assert(AbstractJournal::State::init_by(
            post_aj,
            AbstractJournal::Config::initialize(pre.i().persistent),
        ));
        assert(AbstractCrashAwareJournal::State::next_by(
            pre.i(),
            post.i(),
            Self::i_lbl(pre, post, lbl),
            AbstractCrashAwareJournal::Step::load_ephemeral_from_persistent(post_aj),
        ));
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
