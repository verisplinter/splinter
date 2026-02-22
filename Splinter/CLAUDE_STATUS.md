# Splinter Verification Status

## Refinement Chain (fully compositional)
```
SystemModel<ConcreteProgramModel>
  --[BracketRefinement]--> SystemModelTwo
  --[ModelRefinementTwo]-> CrashTolerantAsyncMap
  --[ModelRefinement_v]--> (thin adapter satisfying RefinementObligation trait)

Where SystemModelTwo.concrete_journal:
  --[ConcreteJournalRefinement]--> AbstractCrashAwareJournal

And ConcreteJournal.jcs_view():
  --[JournalCoordinationRefinement]--> LikesJournal
```

## Where to Pick Up

The most productive next targets, in suggested order:

1. **internal_marshal_refines** (CJR, 1 assume): Marshal moves data from unmarshalled_tail
   to on-disk page via cache. `full_journal() = on-disk decoded ++ tail` should be unchanged.
   This is a JCS-level property: marshal doesn't change `jcs_view().i()`. Unlike the other
   internal ops, marshal updates *both* journal and cache (new page in cache, shorter tail in
   journal). A new JCS public lemma `marshal_preserves_i` is likely needed. Look at the
   existing pattern in `cache_internal_preserves_i` etc.

2. **commit_start_refines / commit_complete_refines** (CJR, 2 assumes): These correspond to
   ACAJ freeze/discard_old steps. commit_start freezes a journal snapshot; commit_complete
   discards old entries. These are real refinement steps (not stutter), so the proof needs to
   construct the ACAJ witness step from the CJ transition.

3. **JCS targeted assumes** (2 assumes): These underpin the CJR internal ops proofs. They need
   cross-component invariants added to JCS:
   - `disk_internal_preserves_i` process_write: "WriteReq addrs for journal pages are in
     dirty_journal_cache (Writeback status)" — ensures ephemeral_disk stable when disk lands writes
   - `cache_disk_ops_preserves_i` writeback_complete: "Writeback entries' data matches disk.content
     at that addr" — ensures removing from dirty cache is safe because disk already has the data

4. **Unknown-ephemeral cases** (4 assume(false)): internal_refines + 3 internal_*_refines else
   branches. ACAJ InternalLabel requires Known ephemeral, but CJ internal transitions don't guard
   on `journal.status is Some`. Options: (a) strengthen CJ guards to require status is Some,
   (b) prove unreachability via invariant, (c) add ACAJ stutter step. This is a design decision.

5. **read_for_recovery_refines** (1 assume): Needs cross-layer chain connecting CachedJournal
   disk reads through JCS→LJ→PJ to invoke PagedJournal::State::read_for_recovery_refines.

6. **crash_refines + load_ephemeral_refines** (2 assumes): BLOCKED by CJ.i() interpretation gap.
   CJ.i() returns `persistent: arbitrary()` when `journal.status is None`. Fix needed in
   ConcreteJournal_v.rs to compute persistent from disk content (superblock's journal extent on
   persistent_journal_disk).

## Current verify.sh Target

`--verify-module implementation::ConcreteJournalRefinement_v`

## Module Verification Counts

| Module | Verified | Errors |
|--------|----------|--------|
| Implementation_v | 38 | 0 |
| ModelRefinement_v | 3 | 0 |
| ModelRefinementTwo_v | 7 | 0 |
| BracketRefinement_v | 2 | 0 |
| ConcreteJournalRefinement_v | 16 | 0 |
| JournalCoordinationSystem_v | 16 | 0 |

## CJR Proof Status (ConcreteJournalRefinement_v.rs)

**Fully proved (0 assumes):**
- `query_lsn_persistence_refines`
- `query_end_lsn_refines` (via full_journal_wf + full_journal_seq_end)
- `put_refines` (via assert_maps_equal! for concat assoc + discard_recent stability)
- `internal_cache_refines` (via JCS cache_internal_preserves_i)*
- `internal_disk_refines` (via JCS disk_internal_preserves_i)*
- `internal_cache_disk_ops_refines` (via JCS cache_disk_ops_preserves_i)*

*These 3 are proved in CJR but depend on 2 targeted assumes in the JCS lemmas they call.

**Remaining assumes (10 total):**
- `read_for_recovery_refines`: assume(includes_subseq)
- `internal_refines`: assume(false) — Unknown ephemeral case
- `internal_marshal_refines`: assume(pre.i()==post.i())
- `internal_cache_disk_ops_refines`: assume(false) — Unknown ephemeral case
- `internal_cache_refines`: assume(false) — Unknown ephemeral case
- `internal_disk_refines`: assume(false) — Unknown ephemeral case
- `commit_start_refines`: assume(false)
- `commit_complete_refines`: assume(false)
- `crash_refines`: assume(false) — blocked by CJ.i() interpretation gap
- `load_ephemeral_refines`: assume(false) — blocked by CJ.i() interpretation gap

## JCS Proof Status (JournalCoordinationSystem_v.rs)

Public proof lemmas (outside state_machine!, callable from CJR):
- `cache_internal_preserves_i`: FULLY PROVEN (no assumes)
- `disk_internal_preserves_i`: 1 targeted assume in process_write case
- `cache_disk_ops_preserves_i`: 1 targeted assume in writeback_complete case

Inductive proofs (inside state_machine!) delegate to the public lemmas above.

Other:
- `initialize`: assume(post.valid_journal_structure()) — needs recovery protocol
- Helper lemmas `cache_lookup_gets_addr` and `cache_filled_entry_in_lookup` proven
  via `Cache::State::build_lookup_map_ensures()` (no assumes)

Proof pattern for CJR calling JCS lemmas:
```
assert(pre.jcs_view().inv());  // derives from CJ.inv() + journal.status is Some
cache_internal_preserves_i(pre.jcs_view(), post.jcs_view(), new_cache);
assert(pre.full_journal() == post.full_journal());  // chains jcs_view().i() =~= through
```

## Other Proof Gaps (lower priority)

- JournalCoordinationRefinement_v: 4 assume(false) + 1 assume(lsns.finite())
- Cache_v: 9 assume(false) stubs (Cache::State::inv_next uses assume(false))
- ModelRefinementTwo_v: ~14 pre-existing assumes (present in original ModelRefinement_v.rs)

## Key Design Decisions
1. ConcreteJournal as `state_machine!` — gives real `next(pre, post, lbl)` predicate
2. Active transitions use JCS-style sub-component steps (not JCS::State::next)
3. crash/load_ephemeral handled at ConcreteJournal level (not through JCS)
4. SystemModelTwo's program_disk uses `valid_disk_transition` wrapper (disk_transition trigger workaround)
5. BracketRefinement uses `from_system_model_atomic` to establish `to_atomic()` equalities
6. ModelRefinement_v.rs keeps delegation methods for backward compat with Implementation_v.rs
7. `sm2_i_lbl` made `open` so adapter can see through it; `sb_landed` made `pub`
8. Adapter's `i_lbl` defined inline on SM1 labels (not via sm2_i_lbl) for label_correspondence proof
9. SM2 program_execute/program_internal explicitly `require new_concrete_journal.disk == pre.concrete_journal.disk`
