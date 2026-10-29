---
title: Let the builder write loop and conditional regions
status: open
labels: [native,x86]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-29
updated: 2026-10-29
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
