# Verified Splinter

Verified Splinter is a verified version of the
[Splinter](https://www.usenix.org/system/files/atc20-conway.pdf)
high-performance key-value store.

The goal of Verified Splinter is to push the envelope of rich, realistic
high-performance systems code verification, both to demonstrate by example
how large systems verification projects can be organized an executed, and
to feed improvements back to verification tools.

Verified Splinter has its origins in the
[Verified BetrFS](https://www.usenix.org/conference/osdi20/presentation/hance) project.
VeriBetrFS and the first versions of Verified Splinter were implemented in Dafny.
[Lessons learned](https://2022.splashcon.org/details/splash-2022-oopsla/4/Linear-types-for-large-scale-systems-verification) in this project motivated the construction of
[Verus](https://github.com/verus-lang/verus) a modern systems verification language built on Rust. Verified Splinter is now built in Verus.

The current version of Verified Splinter is a single-threaded implementation.

# Verified Splinter guarantees

Verified Splinter includes a simple model of the system specification: what outputs
are allowed in response to Put and Get operations.
The source code includes a proof that all of the complexity of the implementation satisfes
that simple model. That proof is checked statically when the code is compiled,
so we know that the specification holds on *every* possible input and execution of the system.

The key-value store in Verified Splinter is guaranteed to be _functionally correct_, i.e. the key-value store always returns correct results.  This also ensures that the VeriBetrFS key-value store is free of low-level bugs, such as buffer overflows, because they would cause the key-value store to deviate from its specified behavior.

In the event of a system crash, the key-value store is guaranteed to only roll back to some prior state that is no older than the last successful sync.  This bounds the amount of data that can be lost, and also guarantees that the key-value store will not come back in an erroneous state after a crash.

The model does not specify any guarantees about liveness or performance.  In other words, we don't prove that Verified Splinter will always respond to requests.  We prove only that, if it does respond, then the result will be correct.

These guarantees are contingent on the correctness of code in the trusted computing base, which includes the compiler, Verus theorem prover, and scaffolding code for interacting with the OS and disk, among other things.

See [docs/Verification.md](docs/Verification.md) for more details.

# Publications

[Verus: A Practical Foundation for Systems Verification.](https://www.microsoft.com/en-us/research/publication/verus-a-practical-foundation-for-systems-verification/)
Andrea Lattuada, Travis Hance, Jay Bosamiya, Matthias Brun, Chanhee Cho, Hayley LeBlanc,
Pranav Srinivasan, Reto Achermann, Tej Chajed, Chris Hawblitzel, Jon Howell, Jay Lorch, Oded
Padon, Bryan Parno. SOSP 2024.

[Verus: Verifying Rust Programs using Linear Ghost Types.](https://www.andrew.cmu.edu/user/chanheec/verus-ghost.pdf)
Andrea Lattuada, Travis Hance, Chanhee Cho, Matthias Brun, Isitha Subasinghe, Yi Zhou, Jon
Howell, Bryan Parno, and Chris Hawblitzel.
OOPSLA 2023.

[Leaf: Modularity for Temporary Sharing in Separation Logic.](https://www.andrew.cmu.edu/user//bparno/papers/leaf.pdf)
Travis Hance, Jon Howell, Oded Padon, and Bryan Parno. OOPSLA 2023.

[Linear Types for Large-Scale Systems Verification](https://2022.splashcon.org/details/splash-2022-oopsla/4/Linear-types-for-large-scale-systems-verification) Jialin Li, Andrea Lattuada, Yi Zhou, Jonathan Cameron, Jon Howell, Bryan Parno, and Chris Hawblitzel. OOPSLA 2022. Distinguished Paper award.

[Storage Systems are Distributed Systems (So Verify Them That Way!)](https://www.usenix.org/conference/osdi20/presentation/hance).  Travis Hance, Andrea Lattuada, Chris Hawblitzel, Jon Howell, Rob Johnson, and Bryan Parno. OSDI 2020.

# Current status

The current source code includes complete atomic state machine models with proofs for the
journal, Bεtree, B+tree, superblock commit coordination, and disk block allocation.

It includes implementations for the trusted I/O framework and basic models of the journal
and map.

# Building and running

Install Verus.

Run `cd Splinter/src; verus sequential_main.rs --compile`.

# Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for our contributing guidelines.
