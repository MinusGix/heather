---
title: Design FunctionIR and its simulate semantics
status: open
labels: [ir, compiler, design]
created: 2026-07-22
updated: 2026-07-22
---

`Compiler::FunctionIR` plus its interpreter is the load-bearing spec object of
the whole language: `Compile` certificates, custom opt passes, and eventual
CPU-model refinement all prove against it. Design it early and deliberately.

Decisions to make:

- Deep embedding as an ordinary inductive datatype *in Heather*, with the
  interpreter an ordinary kerneltime function.
- Call it `simulate`, not `eval`; result-type shaped (must handle divergence
  / stuckness explicitly — fuel/step-indexing for now, possibly trace-shaped
  later per [[effects-direction]]).
- IR is a stability/separation layer: users normally go through builder APIs,
  not raw constructors, so the IR can evolve. "Deep" compiler access exists
  but is explicitly more fragile.
- Versioning: IRs live under versioned subnamespaces (`v1::IR`, `v2::IR`).
  A version bump ships `translate(v1::IR) -> v2::IR` *with a certificate*
  that `v2::simulate(translate(ir))` refines `v1::simulate(ir)`; existing
  Compile instances then transport by composing proofs. Treat this
  composition working out as a stress test of simulate's type.
