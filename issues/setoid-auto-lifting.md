---
title: Setoid auto-lifting via boxed-code introspection (quotient substitute)
status: open
labels: [kernel,metaprogramming,design]
created: 2026-07-23
updated: 2026-07-23
---

Placeholder for a later targeted design round; parked from the 2026-07-23
foundations discussion.

**Decision context:** no quotient former in the kernel (undecided long-term;
setoids get us there). The pain of setoids is the boilerplate: every function
over a setoid carrier needs a respects-the-relation proof threaded through
signatures. The idea: kill most of that boilerplate with a **certifying
generator** rather than a kernel feature — a kerneltime metaprogram that

1. takes a boxed function `□(Δ ⊢ A → B)` plus setoid structures on `A`/`B`,
2. introspects the code and either checks respect *syntactically* (large
   classes of functions respect ≈ for free — e.g. everything built from
   already-lifted operations) or emits the proof obligation it couldn't
   discharge,
3. mints the lifted function together with its respect-proof, as a typeclass
   instance (same shape as [[compile-typeclass-design]] certificates: outputs
   carry proofs, the generator itself is untrusted).

"Auto lifting large classes of functions" is the user's phrase — the syntactic
respect-checker is the interesting research-ish bit (a congruence analysis
over kernel syntax, structurally like the lifetime/uniqueness discipline idea
in the project vision: intensional analyses minting evidence).

Depends on the box/view-layer ergonomics ([[front-end-sugar]]) more than on
any kernel extension. Revisit after the milestone; expand into a real design
then.

## Log

- 2026-07-23: Filed from foundations discussion (see [[kernel-v1-extensions]]
  log of the same date): quotients stay out of the kernel for now, setoids +
  this auto-lifting story are the plan of record.