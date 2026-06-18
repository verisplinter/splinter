---
name: verified-betrfs-proof
description: Use for continuing Verus proof work in the verified-betrfs Splinter checkout, especially allocation journal, caching-disk journal, crash-aware journal/branch, SystemModelTwo/CrashAwareCachingDiskSystem, AnotherAtomicState, or model-refinement tasks. Trigger when the user asks to inspect, repair, refactor, verify, or explain proof obligations, invariants, refinement layers, module-list changes, or journal/branch/cache/disk design decisions in this repository.
---

# Verified BetrFS Proof

## First Moves

Start by reading only the reference files needed for the task:

- `references/current-state.md`: current branch/module focus, recent successful verification, and known paused downstream work.
- `references/proof-principles.md`: user preferences and proof architecture rules.
- `references/allocation-journal.md`: loose allocation-journal model, path-local tight view, and frozen-image facts.
- `references/caching-disk-journal.md`: caching-disk journal expectations when downstream modules are re-enabled.
- `references/verification.md`: targeted commands and workflow.
- `references/new-conversation-brief.md`: pasteable handoff text for a new thread.

Before editing, run a narrow context check:

```sh
git status --short
rg -n "target_symbol_or_module" relevant/files
```

Do not assume the module list is fully enabled. Inspect `implementation/mod.rs` before blaming downstream failures.

## Working Style

- Prefer proving facts at the layer that owns them. For example, AU-page-bound facts about `AllocationJournal::State` belong in `AllocationJournal_v.rs`, not in caching-disk journal refinement.
- Do not add `assume(` or `admit(`.
- Do not change transition definitions unless the user explicitly approves it or asks for that design change.
- If the user asks to focus one layer, comment out or ignore downstream modules rather than spending cycles repairing proofs against a moving contract.
- Keep local/native invariants to facts introduced by the current layer. Put inherited structural facts in refinement/semantic predicates and prove them through refinement when possible.
- Use `apply_patch` for manual edits.
- Run targeted Verus commands after each proof-sized change.

## Proof Triage

When a proof fails, classify it before editing:

- Missing local lemma: package the repeated proof at the owning layer.
- Wrong layer: move the proof obligation up/down rather than rebuilding structural facts in the caller.
- Bad transition contract: stop and explain the exact transition requirement that seems semantically wrong.
- Rlimit/noise: split by operation/case only when the proof strategy is already sound.

Prefer postconditions that callers can directly use. For example, expose a caller-friendly consequence like:

```rust
addr relevant to frozen tight bounds ==> pre.frozen_prefix_domain(frozen).contains(addr)
```

rather than forcing downstream proofs to reconstruct AU-page-bound monotonicity.

## Verification Discipline

Use module-scoped commands first. Avoid full-crate verification until the active layer is stable.

When reporting results, say which modules were verified and whether warnings are only recommendation/trigger warnings. If a command was not run, say that plainly.
