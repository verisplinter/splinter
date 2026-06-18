# Verification Workflow

## Standard Commands

Use targeted verification:

```sh
~/verus/verus main.rs --verify-module module::path --expand-errors --multiple-errors 80 --no-auto-recommends-check
```

For allocation journal work:

```sh
~/verus/verus main.rs --verify-module allocation_layer::AllocationJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationCrashAwareJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationCrashAwareJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
```

For caching-disk journal work, once re-enabled:

```sh
~/verus/verus main.rs --verify-module implementation::CachingDiskJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module implementation::CachingDiskJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module implementation::CrashAwareCachingDiskJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module implementation::CrashAwareCachingDiskJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
```

## Hygiene Checks

Run after proof edits:

```sh
rg -n "assume\\(|admit\\(" allocation_layer implementation
git diff --check
git status --short
```

## Failure Handling

Use expanded diagnostics to locate the exact predicate. Then ask:

- Is this obligation owned by the current layer?
- Is there an upstream refinement lemma that should expose it?
- Is this a true semantic requirement or an artifact of an overly tight interpretation?
- Can a caller-facing postcondition replace a copied proof fragment?

When the verifier reports many downstream failures after changing an upper-layer contract, narrow the active module list and stabilize the owning layer first.

## Communication

Report:

- files changed;
- exact modules verified;
- unresolved blockers;
- whether warnings are just Verus recommendation/trigger warnings.

Do not claim full refinement unless the exact refinement module was verified in the current turn.
