# New Conversation Brief

Paste or summarize this in a fresh conversation when continuing the verified-betrfs proof work.

## Repository

Work in:

```text
/Users/jelly/research/verified-betrfs/Splinter/src
```

Use `rg` for search and `apply_patch` for edits. Check `git status --short` before touching files.

## Current Focus

Focus on allocation journal first. `CachingDiskJournal_v`, `CachingDiskJournalRefinement_v`, `CrashAwareCachingDiskJournal_v`, and `CrashAwareCachingDiskJournalRefinement_v` are intentionally commented out in `implementation/mod.rs` while the allocation-layer contract is stabilized.

The allocation journal model should store and operate on a loose actual disk. Reachable semantic journal facts should come from path-local tight view construction (`path_decodable` / `path_build_tight`), not from a second stored disk.

## User Preferences

- Do not change transition definitions without explicit approval.
- Do not use `.i()` in transition definitions.
- Do not add `assume(` or `admit(`.
- Avoid reproving inherited structural facts in lower layers.
- Prove facts at the owning layer and expose useful postconditions.
- Use targeted Verus commands before broader verification.
- If a proof seems hard because the obligation is at the wrong layer, pause and explain the layer mismatch.

## Recent Proven Bridge

`AllocationJournal::State::frozen_journal_is_valid_image` now exports that every address relevant to the frozen tight image's AU-page bounds is in the live `frozen_prefix_domain`. This bridges frozen tight bounds to live `au_page_bounds`, so downstream prepared-image proofs can use prefix agreement instead of rebuilding the bound proof.

## First Verification Commands

```sh
~/verus/verus main.rs --verify-module allocation_layer::AllocationJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationCrashAwareJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationCrashAwareJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
```

Only after those are stable should the caching-disk journal layer be re-enabled.
