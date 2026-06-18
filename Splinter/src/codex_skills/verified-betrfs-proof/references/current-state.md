# Current State

Use this file to orient a fresh conversation. Verify against the live checkout because branch/module state may drift.

## Latest Focus

The active design focus is the allocation journal loose-disk model with path-local tight journal semantics. Downstream implementation journal modules were temporarily commented out so allocation-layer contracts can stabilize first.

Current active allocation targets recently verified:

- `allocation_layer::AllocationJournal_v`
- `allocation_layer::AllocationJournalRefinement_v`
- `allocation_layer::AllocationCrashAwareJournal_v`
- `allocation_layer::AllocationCrashAwareJournalRefinement_v`

`implementation/mod.rs` currently comments out the caching-disk journal and crash-aware caching-disk journal path:

- `CachingDiskJournal_v`
- `CachingDiskJournalRefinement_v`
- `CrashAwareCachingDiskJournal_v`
- `CrashAwareCachingDiskJournalRefinement_v`

Do not re-enable them unless the user asks to bring the caching-disk layer back.

## Recent Allocation-Layer Lemma

`AllocationJournal::State::frozen_journal_is_valid_image` now also proves the caller-facing AU-page-bound consequence:

```rust
let image = pre.frozen_image(lbl->frozen_journal);
let tight = image.tight_tj();
let tight_bounds = tight.disk_view.build_au_page_bounds_au_walk(tight.freshest_rec, image.first);
forall |addr| {
    let record = image.tj.disk_view.entries[addr];
    image.tj.disk_view.entries.contains_key(addr)
    && tight_bounds.contains_key(addr.au)
    && addr.page <= tight_bounds[addr.au]
    && image.tj.seq_start() < record.message_seq.seq_end
} ==> pre.frozen_prefix_domain(lbl->frozen_journal).contains(addr)
```

This is the bridge needed later by crash-aware caching-disk journal prepared-image proofs: frozen tight bounds are within live `au_page_bounds`, so prefix clean/persistent equality covers the pages `valid_image()` cares about.

## Known Paused Work

The next downstream objective, when re-enabled, is to use the allocation-layer bridge to prove `prepared_image.i().valid_image()` in `CrashAwareCachingDiskJournalRefinement_v` from prefix agreement, instead of reproving structural journal facts at the caching-disk layer.

Do not start there unless the user explicitly asks to resume caching-disk journal.
