# proof_prune

`proof_prune` removes spurious proof-diagnosis `assert(...)` lines by repeatedly re-verifying.

It supports two modes:

1. Single-file mode (`--file` + `--module`)
2. Batch mode across all `.rs` files under a directory (`--all-files`), queued by file.

## Build

```bash
cd Splinter/tools/proof_prune
cargo build
```

## Single-file mode

```bash
cargo run -- \
  --file ../../src/marshalling/ResizableUniformSizedSeq_v.rs \
  --module marshalling::ResizableUniformSizedSeq_v \
  --verus ~/work/verus/source/target-verus/release/verus \
  --entry main.rs \
  --workdir ../../src \
  -- --triggers-mode silent --multiple-errors 2
```

## Batch mode (file-queued waves)

```bash
cargo run -- \
  --all-files \
  --verus ~/work/verus/source/target-verus/release/verus \
  --workdir ../../src \
  --entry main.rs \
  --jobs 4 \
  --wave-size 8
```

Optional wave snapshot command:

```bash
--snapshot-cmd "git commit -am 'proof_prune wave checkpoint'"
```

## What it considers as candidate asserts (v1)

- Single-line `assert(...)` statements
- Not already labeled

It skips:

- `assert forall ...`
- `assert exists ...`
- asserts already labeled via inline or preceding comment containing `trigger`, `witness`, or `keep`

## Batch safety model

- Queue is by **file** (not function)
- Workers use isolated `git worktree` directories under `/tmp`
- After each wave:
  1. workers drain
  2. changes merge into main worktree
  3. optional snapshot command runs

Note: full-system wave-level global verification is currently disabled by design to allow
uninterrupted full-pass pruning. Resolve any cross-file conflicts at the end.

## Useful knobs

- `--function <substr>`: limit pruning to function names containing substring (repeatable)
- `--label <text>`: default `trigger`
- `--stream-verus`: stream verifier output live for every function check

## Limitations

- Text-scanning parser (not full Rust AST)
- Wildcard verify selection (`*fn_name*`), so highly-colliding function names may verify more than expected
- Sequential per-file processing by design (parallelism is file-level)
