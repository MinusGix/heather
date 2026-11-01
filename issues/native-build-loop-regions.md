---
title: Let the builder write loop and conditional regions
status: closed
labels: [native,x86]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-29
updated: 2026-10-31
---

The builder (`lib/native/native_build.hthr`) cuts its nodes into dataflow
leaves (`List::takes`) and writes every loop as a statement `Repeat`. The
compiler now takes `Sequence`, `Compose`, `Conditional` and `Loop` regions
inside a leaf ([[native-compile-wider-leaves]], 2026-10-29), proved once, so
a builder that emits them could inline a helper with a conditional or a
bounded loop (plan §3.3: "Inlined regions with conditionals or loops need
§3.4") and write a byte map as a FunctionIR loop instead of a `Repeat` of
statements.

## Scope

- A builder form for a bounded loop over words (count, parameters, next
  state, exit bit) lowering to `Loop`, and one for a conditional lowering to
  `Conditional`, each in counted/scoped form (`StructuredRegion::scoped`),
  so what the builder writes is what the compiler takes.
- A tool rewritten with it (tr's byte map is the natural first), with the
  lowering fixed in `lib/_tests/native/native_build_tests.hthr`.

## Log

- 2026-10-31: 2026-10-31: hih-tools closed (docs/compiler-milestones-proposal.md §8). Moved to nh-front: [[runtime-fn-setups-design]] folds this in or closes it.
<<<<<<< HEAD
- 2026-10-31: 2026-10-31: `docs/runtime-fn-setups-design.md` §10: kept as a near-term builder ergonomics win. Once R5 lands, loops and conditionals a `runtime fn` can express are written there and lowered to `Loop`/`Conditional` by the default setup; the builder forms retire with the builder in R6.
=======
- 2026-10-31: Done on branch claude/project-thread-xhabhy: `Calc` (native_build) writes assignments, byte stores, `choose`/`only_if` and `passes`/`count_up` over words, and `compute` runs one as a statement lowered to one scoped region (a Conditional, a counted Loop over its state words in place). tr's byte map is one such loop and write-elf compiles it; lowerings, scoping, a negative control (a pass reading a word outside its state) and runs are fixed in lib/_tests/native/native_build_tests.hthr. Found on the way: native_alloc keys loop sets by the loop's control word, and builder siblings number from the same `next`, so a count could share a later `do … while`'s test-bit id and be live after its own loop (refused, reason 13); the builder clears every count after its loop.
>>>>>>> origin/master
