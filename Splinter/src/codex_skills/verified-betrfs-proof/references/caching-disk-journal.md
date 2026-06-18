# Caching-Disk Journal Notes

This layer is currently paused/commented out in `implementation/mod.rs` while allocation journal contracts stabilize.

## Intended Role

`CachingDiskJournal` should refine to `AllocationJournal` by interpreting the caching disk overlay as the allocation journal loose disk.

The layer should add only cache-specific ideas:

- raw-page cache/persistent maps;
- clean/evictable checks;
- load-index from partial reads;
- AU discovery and free-set interaction at composers;
- cache forget/mark-clean/access effects.

It should not reprove all path-local journal structure if the allocation layer already exports the needed facts.

## Commit Prepared Direction

For journal commit prepared, the desired shape is:

1. `CommitStart` records frozen metadata.
2. `CommitPrepared` performs cached-journal/caching-disk checks only.
3. Prepared concrete image may use persistent raw pages restricted to frozen loose AUs.
4. Only prefix pages need live/persistent agreement.
5. Allocation-layer lemmas prove that those prefix pages cover everything `valid_image()` cares about.

Do not compare or require equality for arbitrary same-AU tail garbage.

## Proof Strategy When Re-enabled

At the crash-aware caching-disk refinement site, do not rebuild AU-page-bound monotonicity. Instead:

- invoke the component `CachingDiskJournal::State::next(... CommitPrepared ...)`;
- obtain cache/persistent prefix equality from `addrs_clean_or_evictable(frozen_prefix_domain)`;
- map concrete frozen metadata to `JournalMetadata`;
- call allocation-layer frozen-image lemmas through `self.ephemeral->v.i()`;
- prove `prepared_image.i().valid_image()` and `acceptable_frozen_image(...)`.

If this becomes difficult, first check whether the allocation-layer lemma postcondition is too weak for the caller.

## Things To Avoid

- Do not put semantic path-walk obligations into `CachingDiskJournal::inv()` unless they are truly native to caching disk.
- Do not make `CommitPrepared` validate the entire loose AU image.
- Do not require arbitrary tail garbage to match persistent disk.
- Do not reintroduce `lsn_addr_index` as cached/allocation journal state.
