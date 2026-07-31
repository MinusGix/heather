---
title: Design FunctionIR and its simulate semantics
status: open
labels: [ir, compiler, design]
created: 2026-07-22
updated: 2026-07-31
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

## Log

- 2026-07-26: Deferred behind round two of [[frontend-roadmap]], deliberately. [[stress-proof-suite]] is closed and its acceptance clause says this reopens in-language, but two of its inputs are still elaborator machinery rather than language features: there is no polymorphism at all ([[surface-polymorphism]] -- an IR generic in anything cannot be written), and the surface's only indexed type is the BUILT-IN Vec, with literal-only lengths and no eliminator ([[indexed-families]], which also has to settle whether indexed finitary families ford over Wf or come from indexed W -- a contradiction this issue's typed-IR design would otherwise have to resolve on the fly). A fuel-indexed simulate does not NEED any of that, which is exactly the risk: it would be writable today and would bake the current limits into the first real consumer. Reopen after roadmap items 11-14.
- 2026-07-28: When this lands, it owns adding the thesis-shaped bench fixture: conversion discharging `simulate ir fuel` against its result at realistic program size and fuel, into the kernel suite ([[kernel-benchmarks]], now closed -- the suite is built; a new family is a ~30-line file in crates/kernel/benches/kernel/fixtures/). Meanwhile conv/computed-numeral is the proxy, and it already carries a warning for this design: with substitution copying payloads ([[subst-copies-payloads-at-depth-zero]]) a fuel-indexed evaluator is quadratic in fuel even though its definition is linear, so simulate's cost model should be checked against that fix rather than assumed.
- 2026-07-31: Design sketch written: docs/ir-simulate-design.md. Decisions: term-form RVSDG (let-normal regions, structured over SSA, term over graph); constructor-tree value domain with per-type embeddings; multi-output as multi-slot binding, no tuple values; Ref = raw Nat + explicit Stuck in v1, intrinsically scoped-then-typed syntax as the recorded target gated on [[sprop-strict-prop]]; fuel private to simulate behind a converges/refines/fuel_monotone interface, equiv discharged at computed bounds; no Prim node, no effects nodes in v1. Partiality futures (Delay, later modality, Bove-Capretta) re-homed to [[effects-direction]]. Acceptance sketch and bench-fixture obligation are the doc's section 11.
- 2026-07-31: Implementing round, part 1 (doc section 11 items 1, 2, 6): lib/ir_v1.hthr lands green -- the first real Heather library file. Datatypes (chain-encoded, section 13 note 1), the fuel-curried interpreter with single-ih dispatch (notes 2-4), embed_nat, and add-as-a-theta-loop, with positive theorems (add(1,1) through the loop, identity through LetCall) and in-language negative controls, all by refl at literal fuel. CI: crates/elab/tests/ir_v1.rs (declarations + wrong-claim refutation always on; full acceptance #[ignore]d for budget, see [[simulate-conversion-cost]] -- filed this round, with measurements: ~2s+/executed step, superlinear in depth). Items 3-4 (converges/fuel_monotone/refines/forall-args equiv) deferred with the route sketched in doc section 13: fuel_monotone is match-recursion's deferred IH-generalization case; the explicit-motive manual route exists and is a session of its own.
