# Allocation Journal Notes

## Core Shape

`AllocationJournal::State` stores one loose actual disk:

```rust
disk_view: DiskView
```

The semantic journal is derived through a path-local tight view rooted at `freshest_rec`, not stored separately.

Important concepts:

- `DiskView::path_decodable(root)`: only reachable path needs structural validity.
- `DiskView::path_build_tight(root)`: constructs the reachable semantic subdisk.
- `JournalImage::tight_tj()`: image semantic journal.
- `JournalImage::valid_image()`: loose image validity plus path-local tight facts.
- `AllocationJournal::State::semantic_inv()`: inherited semantic facts needed for refinement.
- `AllocationJournal::State::refinement_inv()`: `inv() && semantic_inv()`.

## Frozen Images

`JournalMetadata` carries:

```rust
boundary_lsn: LSN
seq_end: LSN
freshest_rec: Pointer
first: AU
```

The frozen loose domain is AU-bounded:

```rust
frozen_loose_domain(meta) = addresses_in_aus(frozen_lsn_au_index(meta).values())
```

The prefix domain is the AU-bounded part covered by live `au_page_bounds`:

```rust
frozen_prefix_domain(meta) =
    addr in frozen_loose_domain(meta)
    && au_page_bounds.contains_key(addr.au)
    && addr.page <= au_page_bounds[addr.au]
```

`acceptable_frozen_image(meta, image)` requires metadata equality, loose domain bounded by frozen AUs, prefix agreement with the live disk, and `image.valid_image()`.

## Key Lemmas

`frozen_journal_is_valid_image(pre, post, lbl)` proves that `pre.frozen_image(lbl->frozen_journal)` is valid and that the frozen tight image is a subdisk of the live semantic journal.

It also exports the bridge that downstream commit-prepared proofs need:

```rust
addr relevant to frozen tight bounds
==> pre.frozen_prefix_domain(frozen).contains(addr)
```

`acceptable_frozen_image_matches_frozen_image(pre, frozen, image)` proves that an acceptable loose image has the same tight semantic image as `pre.frozen_image(frozen)`.

## Verification Targets

Verify allocation layer before downstream implementation layers:

```sh
~/verus/verus main.rs --verify-module allocation_layer::AllocationJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationCrashAwareJournal_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
~/verus/verus main.rs --verify-module allocation_layer::AllocationCrashAwareJournalRefinement_v --expand-errors --multiple-errors 80 --no-auto-recommends-check
```

Recommendation warnings are common around spec-function recommends and trigger choices; do not treat them as failures unless the user asks for warning cleanup.
