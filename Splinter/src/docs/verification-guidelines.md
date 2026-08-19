# Verification Guidelines

## Reveal Discipline

- Do not call `reveal` or `reveal_with_fuel` for an open/default spec
  function. Its definition is already available to Verus.
- A reveal is justified only when the target declaration is explicitly opaque,
  such as a `closed spec fn` or a function marked `#[verifier::opaque]`.
- For state-machine generated functions, reveal only `State::init`,
  `State::init_by`, `State::next`, and `State::next_by`. The initialization
  relations are explicitly opaque in the Verus state-machine macro. Do not
  reveal individual initializers, transitions, or generated helper relations.
- If removing a reveal exposes a proof failure, first repair the proof boundary,
  postcondition, or supporting lemma. Do not restore a reveal unless the target
  is explicitly opaque under the rules above.
- Existing bounded `reveal_with_fuel` calls used by the recursive branch
  `fold_left_alt` proofs and Betree sequence-to-write-map proofs are documented
  exceptions. Do not expand this exception set without first checking whether
  a one-step equation lemma gives a cleaner proof boundary.
