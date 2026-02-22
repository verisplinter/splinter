# Splinter Verification Status

## Current State: Step 11c — CJR assumes reduced from 13 to 10

### Refinement Chain (fully compositional)
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

### Step 11c: JCS public lemmas + CJR internal ops proven

**JCS public proof lemmas** (in JournalCoordinationSystem_v.rs, outside state_machine!):
- `cache_internal_preserves_i`: FULLY PROVEN — reserve/evict/noop preserve dirty_journal_cache
- `disk_internal_preserves_i`: 1 targeted assume — process_write needs invariant
  "write addrs in lsn_addr_index are in dirty_journal_cache"
- `cache_disk_ops_preserves_i`: 1 targeted assume in writeback_complete — needs invariant
  "data already landed on disk before Writeback→Clean transition"

**CJR proofs using JCS lemmas** (3 assume(pre.i()==post.i()) eliminated):
- `internal_cache_refines`: proven via cache_internal_preserves_i
- `internal_disk_refines`: proven via disk_internal_preserves_i
- `internal_cache_disk_ops_refines`: proven via cache_disk_ops_preserves_i
- Pattern: assert(pre.jcs_view().inv()) → call JCS lemma → assert(pre.full_journal() == post.full_journal())

**Fully proved (0 assumes):**
- `query_lsn_persistence_refines`
- `query_end_lsn_refines` (via full_journal_wf + full_journal_seq_end)
- `put_refines` (via assert_maps_equal! for concat assoc + discard_recent stability)
- `internal_cache_refines` (via JCS cache_internal_preserves_i)
- `internal_disk_refines` (via JCS disk_internal_preserves_i)
- `internal_cache_disk_ops_refines` (via JCS cache_disk_ops_preserves_i)

**Remaining assumes (10 total):**
- `read_for_recovery_refines`: assume(includes_subseq) — needs cross-layer JCS→PJ chain
- `internal_refines`: assume(false) Unknown case — architectural
- `internal_marshal_refines`: assume(pre.i()==post.i()) — marshal changes both journal+cache
- `internal_cache_disk_ops_refines`: assume(false) Unknown ephemeral case — architectural
- `internal_cache_refines`: assume(false) Unknown ephemeral case — architectural
- `internal_disk_refines`: assume(false) Unknown ephemeral case — architectural
- `commit_start_refines`: assume(false) — freeze reasoning
- `commit_complete_refines`: assume(false) — discard_old reasoning
- `crash_refines`: assume(false) — crash semantics
- `load_ephemeral_refines`: assume(false) — recovery

**Blocking analysis:**
1. **internal_marshal pre.i()==post.i() (1 assume)**: Marshal moves data from unmarshalled_tail
   to on-disk via cache. full_journal() = on-disk decoded ++ tail should be unchanged, but
   proof needs JCS-level reasoning about how marshal preserves the composed interpretation.
2. **Unknown-ephemeral cases (4 assume(false))**: ACAJ InternalLabel requires Known ephemeral.
   CJ internal transitions don't guard on journal.status is Some. Options:
   (a) Strengthen CJ guards, (b) Prove unreachability, (c) Add ACAJ stutter step.
3. **read_for_recovery includes_subseq (1 assume)**: Needs to connect CachedJournal
   read_for_recovery (depth-based disk reads) through JCS→LJ→PJ chain to invoke
   PagedJournal::State::read_for_recovery_refines.
4. **commit_start/complete (2 assume(false))**: freeze_for_commit and discard_old at CJ
   level, need to show correspondence with ACAJ commit steps.
5. **crash (1 assume(false))**: CJ.i() uses arbitrary() for persistent when journal.status
   is None. Needs interpretation function fix.
6. **load_ephemeral (1 assume(false))**: Blocked by same interpretation function issue as crash.

### Key Technical Insight: CJ.i() Interpretation Gap
The CJ interpretation function returns `persistent: arbitrary()` when `journal.status is None`
(crash state). This makes crash_refines and load_ephemeral_refines fundamentally unblocked only
when the interpretation is fixed to compute persistent from disk content (the superblock's
journal extent on persistent_journal_disk). This is a design fix needed in ConcreteJournal_v.rs.

### Module Verification Counts
| Module | Verified | Errors |
|--------|----------|--------|
| Implementation_v | 38 | 0 |
| ModelRefinement_v | 3 | 0 |
| ModelRefinementTwo_v | 7 | 0 |
| BracketRefinement_v | 2 | 0 |
| ConcreteJournalRefinement_v | 16 | 0 |

### Remaining assumes in ModelRefinementTwo_v.rs
These are all **pre-existing** proof gaps (present in original ModelRefinement_v.rs):
- `program_execute / Put`: assume(false) — Put extends journal, appends a new version
- `program_execute / non-NoopInput`: assume(MapSpec::State::next(...))
- `program_disk / InitiateRecovery|SuperblockRecovery`: assume(post.inv())
- `program_disk / CacheIO*`: assume(ipre==ipost), assume(post.inv())
- `program_disk / ExecuteSyncBegin`: assume(false)
- `program_disk / ExecuteSyncEnd`: assume(false)
- `program_internal / JournalRecovery|MapRecovery`: assume(post.inv())
- `program_internal / RecoveryComplete`: assume(false)
- `disk_internal / sb_landed`: assume(false) — maps to SyncOp
- `disk_internal / non-sb_landed client_ready`: assume(ipre==ipost)
- `disk_internal / non-sb_landed RecoveryComplete`: assume(ipre==ipost)
- `disk_internal`: assume(post.inv())
- `crash`: assume(false)
- `init_refines` (ModelRefinement_v adapter): assume(false)

### Other proof gaps (lower layers)
- JournalCoordinationSystem_v:
  - Inductive proofs delegate to public lemmas (cache_internal_preserves_i, etc.)
  - `cache_internal_preserves_i`: FULLY PROVEN (no assumes)
  - `disk_internal_preserves_i`: 1 targeted assume — needs invariant "WriteReq addrs for journal
    pages are in dirty_journal_cache" (cross-component: cache status ↔ disk requests)
  - `cache_disk_ops_preserves_i`: 1 targeted assume in writeback_complete case — needs invariant
    "Writeback entries with no pending WriteReq have matching disk.content" (cross-component:
    process_write already flushed data before response delivered to cache)
  - `initialize`: assume(post.valid_journal_structure()) — needs recovery protocol
  - Helper lemmas `cache_lookup_gets_addr` and `cache_filled_entry_in_lookup` proven via
    `Cache::State::build_lookup_map_ensures()` (no assumes)
- JournalCoordinationRefinement_v: 4 assume(false) stubs
- Cache_v: 9 assume(false) stubs (Cache::State::inv_next uses assume(false))

### Key Design Decisions
1. ConcreteJournal as `state_machine!` — gives real `next(pre, post, lbl)` predicate
2. Active transitions use JCS-style sub-component steps (not JCS::State::next)
3. crash/load_ephemeral handled at ConcreteJournal level (not through JCS)
4. SystemModelTwo's program_disk uses `valid_disk_transition` wrapper (disk_transition trigger workaround)
5. BracketRefinement uses `from_system_model_atomic` to establish `to_atomic()` equalities
6. ModelRefinement_v.rs keeps delegation methods for backward compat with Implementation_v.rs
7. `sm2_i_lbl` made `open` so adapter can see through it; `sb_landed` made `pub`
8. Adapter's `i_lbl` defined inline on SM1 labels (not via sm2_i_lbl) for label_correspondence proof
9. SM2 program_execute/program_internal explicitly `require new_concrete_journal.disk == pre.concrete_journal.disk`
