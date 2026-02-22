# proof_prune

`proof_prune` is a conservative helper for cleaning up proof-diagnosis asserts.

It scans one Rust/Verus source file, works function-by-function, and for each unlabeled single-line
`assert(...)` candidate it:

1. Removes the line.
2. Re-runs Verus on that function (`--verify-only-module + --verify-function`).
3. If verification still passes, keeps the line removed.
4. If verification fails, restores the line and appends `// trigger` (or custom label).

## Build

```bash
cd Splinter/tools/proof_prune
cargo build
```

## Usage

```bash
cargo run -- \
  --file ../../src/marshalling/ResizableUniformSizedSeq_v.rs \
  --module marshalling::ResizableUniformSizedSeq_v \
  --verus ~/work/verus/source/target-verus/release/verus \
  --entry main.rs \
  --workdir ../../src \
  -- --triggers-mode silent --multiple-errors 2
```

### Arguments

- `--file`: source file to edit
- `--module`: module path for `--verify-only-module`
- `--verus`: Verus binary path
- `--entry`: Verus entry file (default `main.rs`)
- `--workdir`: command working directory for Verus (default current directory)
- `--label`: label added to required asserts (default `trigger`)
- `--function`: optional function-name substring filter (repeatable)
- `--`: remaining args are passed through to Verus

## Label heuristic (v1)

Asserts are skipped if they are already labeled by:

- an inline comment containing `trigger`, `witness`, or `keep`, or
- the nearest preceding non-empty comment line containing `trigger`, `witness`, or `keep`.

## Current limitations

- Only handles **single-line** `assert(...)` statements.
- Skips `assert forall ...` and `assert exists ...` forms.
- Uses wildcard verify-function matching (`*fn_name*`), which may verify more than one function if names overlap.
- Parses with conservative text scanning (not a full Rust AST).
- Runs sequentially (no worktree-based parallelism yet).
