# Proof Principles

## Layer Ownership

Prove facts at the layer that owns the state.

- Allocation journal owns `lsn_au_index`, `au_page_bounds`, `mini_allocator`, frozen metadata, and loose journal disk semantics.
- Caching-disk journal owns cache/persistent composition, clean/evictable checks, and raw-page decoding boundaries.
- Crash-aware wrappers should mostly manage protocol state: persistent, ephemeral, frozen/prepared flags, commit/crash movement.
- System-level modules should orchestrate submachines and free-set/superblock bookkeeping, not decode branch/journal values.

If a downstream proof is reconstructing an upstream structural fact, look for a missing lemma/postcondition at the upstream layer.

## Invariant Split

Use one native invariant for facts introduced by the state machine itself. Keep inherited semantic properties in a refinement/semantic predicate when they are only needed to prove refinement.

Preferred shape:

```rust
state.inv()              // local inductive facts
state.semantic_inv()     // inherited/refinement facts, proven through refinement
state.refinement_inv()   // inv && semantic_inv
```

Do not independently prove a large `semantic_inv_next` path if the same fact can be obtained by proving the step refines and then using the target layer's invariant. The user strongly dislikes reproving the same structural facts across layers.

## Transitions

- Do not change transition definitions without explicit user approval.
- If a transition seems semantically wrong, stop and explain the exact issue.
- Do not use `.i()` inside transition definitions.
- Composers should invoke submachines through `State::next(...)`, not named inner transitions or `next_by(...)` in specs. Proofs may reveal `next`/`next_by` when necessary.
- Avoid revealing transition bodies that are not state-machine `next`/`next_by`; it usually adds noise.

## Loose vs Tight Journal

Use the loose disk for actual stored state and transition enabling/updating. Use a path-local tight view only to express reachable journal semantics and inherited structure.

The intended model:

- Loose disk may contain unreachable typed garbage in journal-owned AUs.
- `path_decodable(root)` only constrains the reachable root path.
- `path_build_tight(root)` is the canonical semantic view.
- `JournalImage::valid_image()` should tolerate loose backing garbage while requiring the path-local tight journal to be valid.
- Frozen metadata is metadata first; commit/crash may accept loose images as long as the allocated prefix agrees with the live image and the relaxed image is valid.

## Proof Ergonomics

When a repeated proof fragment appears, package the strongest useful caller-facing fact. Good lemmas say what the caller needs, not how the proof internally walked the journal.

Prefer:

```rust
frozen tight bounded page ==> live frozen_prefix_domain contains page
```

over:

```rust
tight_bounds[au] <= live_bounds[au]
```

unless the latter is directly what all callers need.

When hitting rlimits, split proofs by operation or step case. Do not split endlessly if the underlying strategy is questionable.
