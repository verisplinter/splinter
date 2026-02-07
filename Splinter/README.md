# Verified SplinterDB Implementation

This project is an implementation of the
(SplinterDB key-value store)[https://splinterdb.org/]
statically verified to maintain functional correctness and
crash safety for every possible execution.

## Motivation and Design

This work follows on
(VeriBetrFS)[https://github.com/vmware-labs/verified-betrfs] which appeared at
(OSDI 2020)[https://www.usenix.org/conference/osdi20/presentation/hance].
VeriBetrFS didn't achieve the performance we wanted, due to several simplifying
compromises. This Splinter design improves on VeriBetrFS with:

    * small cache granularity (4K vs 8MB) to increase the cache size measured
      by count of leaves,
    * page-managed cache units to avoid malloc-incurred external fragmentation
      and need for overprovisioned headroom,
    * incremental parsing (pointer chasing) to minimize compute work reading data out of tree leaves

The VeriSplinter work also had a confusing, irregular proof organization.
One of our goals in this work was to demonstrate that a small toolkit
(refinement and composition of labeled-transition atomic state machines)
is sufficient to organize all of the modules, even as VeriSplinter design
has greater complexity than VeriBetrFS.

## Evolution

VeriBetrFS reasoned about I/O concurrency and nondeterministic crashes.
Our initial goal with Verified Splinter was to remain focused
on a single-threaded implementation.

Concurrent with this work, Hance et al developed
(VerusSync)[https://www.andrew.cmu.edu/user/bparno/papers/hance_thesis.pdf]
which provides a way to refine a shared-memory concurrent implementation to an
atomic state machine model. While VeriSplinter is still single-threaded, we
employ VerusSync to enable a more natural binding between the implementation
code and the atomic state machine models than appeared in the predecessor
systems.

We began building this work in Dafny. As the (Verus)[https://github.com/verus-lang/verus] language improved -- in no small part due to feedback from this work! -- we ported all of our state machine models into Verus and
built the implementation there. You can still find the original Dafny
models in the git history.

## Proof Layout

For a diagram of the refinement proof structure we're building in the `verus` see [`splinter/docs/refinement-hierarchy.svg proof`](https://github.com/vmware-labs/verified-betrfs/blob/splinter/docs/refinement-hierarchy.svg).

# Setting up first verification/build

Get the verisplinter source:
```
git clone git@github.com:verisplinter/splinter.git
```

Get a [verus binary](https://github.com/verus-lang/verus/releases).
For example:
```
mkdir verus-install
cd verus-install
wget https://github.com/verus-lang/verus/releases/download/release%2F0.2026.01.30.44ebdee/verus-0.2026.01.30.44ebdee-x86-linux.zip
unzip verus-0.2026.01.30.44ebdee-x86-linux.zip
rustup install 1.93.0-x86_64-unknown-linux-gnu # or whatever version verus demands
ln -sf $(pwd)/verus-x86-linux/cargo-verus ~/.cargo/bin/cargo-verus
cd ..
```

Verify & build:
```
cd splinter/Splinter
cargo verus verify
```

(If the version of verus you downloaded doesn't match Cargo.toml from
the repo, you may need to update Cargo.toml.)

## Handy commands

`$verus -Zunpretty=expanded bundle.rs` to get expanded macro representation of a verus file.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs`
To verify just a single module.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 1`

To disable "Recommends" checks (since `verus` will sometimes incorrectly warn about recommends clauses
not being satisfied when they are provably satisfied).
```
--no-auto-recommends-check
```

If you find yourself buried in error output, use this command to only get the top (and also get it in color):
```
$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 2 --color=always 2>&1 | head -n 50
```

### Pushing `.record-history` History

If you're using the `record-history` feature of verus, here's instructions for how to push the history:
```
cd .record-history/git
RECORDED_ITEMS=`git log --all | grep 'record-history-ref-hash' | wc -l`
echo Recorded $RECORDED_ITEMS verus runs, pushing...
git push --all target
echo Pushed all branches.
```

