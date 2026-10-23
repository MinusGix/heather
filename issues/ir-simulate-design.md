---
title: Design FunctionIR and its simulate semantics
status: closed
labels: [ir, compiler, design]
created: 2026-07-22
updated: 2026-08-01
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
- 2026-07-31: Implementing round, part 1 (doc section 11 items 1, 2, 6): lib/certgen/ir_v1.hthr lands green -- the first real Heather library file. Datatypes (chain-encoded, section 13 note 1), the fuel-curried interpreter with single-ih dispatch (notes 2-4), embed_nat, and add-as-a-theta-loop, with positive theorems (add(1,1) through the loop, identity through LetCall) and in-language negative controls, all by refl at literal fuel. CI: crates/elab/tests/ir_v1.rs (declarations + wrong-claim refutation always on; full acceptance #[ignore]d for budget, see [[simulate-conversion-cost]] -- filed this round, with measurements: ~2s+/executed step, superlinear in depth). Items 3-4 (converges/fuel_monotone/refines/forall-args equiv) deferred with the route sketched in doc section 13: fuel_monotone is match-recursion's deferred IH-generalization case; the explicit-motive manual route exists and is a session of its own.
- 2026-07-31: Section 11 item 5 done, adapted: the kernel suite gains conv/simulate-payload and conv/simulate-depth (crates/kernel/benches/kernel/fixtures/simulate.rs) -- the cost mechanism hand-built, since elaborator output cannot enter the zero-dep kernel suite; the realistic-scale number lives with [[frontend-benchmarks]] (time heather check on lib/certgen/ir_v1.hthr). Baseline re-saved. Depth is linear at constant per-step work (0.97), payload is the defect axis (0.91, should be ~0) -- ir_v1's superlinearity is growing state, not fuel recursion itself.
- 2026-07-31: The #[ignore] is gone: [[simulate-conversion-cost]] closed with definitions, and crates/elab/tests/ir_v1.rs now runs the full acceptance under scripts/test (64s debug, was ~18 minutes; 2.1s for the release heather check, was 107s at filing). The file's own comments are updated with the current numbers, and the loop/call split is kept for a smaller reason than before -- the combined add(2,3)-through-LetCall path is ~24s rather than >300s, affordable but not routine-gate material.
- 2026-07-31: Step-machine round: attempted, measured, ABANDONED -- the interpreter stays recursive and doc section 13 gains note 6 as a dated amendment. The plan was to defunctionalize simulate (Config = env x Ir x continuation-frame chain, one non-recursive step, run iterating on fuel in tail position) to route around [[whnf-sharing-term-growth]]'s exponential and finally land add(2,3)-through-LetCall as a routine theorem. The machine was built to every discipline this design records (fuel-only recursion, single ih occurrence, tail application, halting configurations sticky so unused fuel stays free -- verified, fuel 20 vs 400 identical) and came out strictly worse: declarations alone 4.9s vs 0.55s, and every sub-region RETURN exponential, so an 8-deep LetCall chain (0.76s / 10 MB recursive) died at the 8 GB cap, and add(a,1) died one loop iteration earlier than the recursive version. Full probe and isolation tables in [[whnf-sharing-term-growth]]; the sharp one is that replacing a configuration field by a semantic IDENTITY wrapper turns flat into ~x2 per level. lib/certgen/ir_v1.hthr is unchanged on master (1.39s release check, green). Section 11 item 5's bench obligation is re-aimed: it needs a depth-of-nesting family, not more fuel or payload.
- 2026-07-31: The §11 item 5 bench obligation is RETIRED, and note 4's discipline is demoted, both by the NbE round ([[nbe-conversion-round]]). The obligation as re-aimed in the last entry ('it needs a depth-of-nesting family, not more fuel or payload') is not buildable as the ~30-line kernel family this issue's 2026-07-28 entry imagined and is no longer worth building: four hand-built kernel families failed to reproduce the nesting axis at all (docs/nbe-conversion-design.md §12), its instrument is scripts/probe-whnf-sharing at the CLI (which §12 argues cannot be a kernel bench -- the assertion is a ratio between adjacent levels, and a wall-clock threshold in a test rots), and its subject no longer exists: simulate is flat. The original thesis-shaped fixture stands as conv/simulate-payload and conv/simulate-depth, both of which kept their slopes across the round. Recorded as a dated amendment in doc §13 note 6 and inline at §11 item 5. Separately, doc §13 note 4's 'one ih occurrence, by measurement' is corrected in place with measured-then vs now: the ~50ms-per-executed-step-per-occurrence cliff (0.24s -> 13.7s at ten occurrences) is now 1.24x for six occurrences instead of one, because a duplicated occurrence evaluates to a shared value rather than a copied term. lib/certgen/ir_v1.hthr keeps its single-ih shape -- restructuring the library to exploit this is a round of its own and nobody has funded it -- but new Heather code is no longer required to obey the discipline. The file also gained the two combined LetCall-into-the-loop theorems that the old cost model forbade (§11 item 2 is now discharged on ONE deep path rather than two short ones) and checks in 1.25s at 14.4 MB peak; its elab test is 9.2s debug.
- 2026-07-31: **Section 11 items 3-4 land**: converges/fuel_monotone/refines and the first forall-args equiv, all in lib/certgen/ir_v1.hthr (one file, because there is no module system and a sibling would have to duplicate every declaration). What is proved: `step_mono` (one step is monotone in its recursive call -- the whole case analysis, eight arms over Ir, non-recursive); `eval_mono_succ` and `eval_mono_plus` (fuel_monotone in the `+ k` shape, by induction on fuel with env/ir/the answer generalized); `le_add` and `fuel_monotone` (the section 6 verbatim shape, with `n <= m` spelled `leb(n)(m) = True` since the prelude has no order on Nat); `refines_refl`/`refines_trans` in the BOUNDED shape plus a three-link concrete chain (add-as-theta-loop, a LetCall to it, a LetCall to that) composing at `plus2 . plus2`; and `add_equiv`, forall a b, at the computed bound `add(a, 5)`, via a loop-invariant lemma (`add_loop_runs`, accumulator generalized) and an embedding lemma (`bumps_embed`). `add_equiv_at` is the same certificate at any larger fuel, fuel_monotone doing the bridging -- section 6's "discharge at a computed bound, monotonicity bridges to the stated form", end to end.

  STATEMENT-SHAPE DEVIATIONS, recorded as doc section 13 note 7 and owned by the new [[surface-existential]]: `converges` is NOT statable as the exists-closure -- the surface has no Sigma indexed by a value, so it takes the computed-bound form -- and `refines` therefore carries a fuel map rather than an existential. Transitivity survives exactly (it is composition of the maps) which is what the section 6 stress test was for. Neither is a named definition, because a `fn` body is an expression and `->` is not an expression.

  ONE SURFACE CHANGE, and it was load-bearing: a motive body is now parsed with the TYPE grammar, so `match fuel as lambda f => (env: Val) -> ...` parses at all. Backwards compatible (the type grammar falls through to the expression grammar for equations, names, applications); tests in crates/elab/tests/motives.rs. Also `absurd`/`inj` now reduce both endpoints before reading constructors off them, because a fuel induction's base case reaches `OutOfFuel = Out(vs)` by computing.

  COST: the release check goes 1.31s / 14.2 MB -> 26.9s / 18.6 MB, ~18s of which is `step_mono`; the elab test goes 9.2s -> 165 CPU-seconds against scripts/test's 300s rail. The measurement [[ih-generalization]] asked for is logged there: the generalized-motive tax is term SIZE per arm, memory barely moved, and it does NOT contradict [[nbe-conversion-round]]'s demotion of the single-ih discipline (a duplicated ih evaluates to a shared value; a bigger motive is bigger before anything evaluates). Negative controls per docs/testing-generated-terms.md are in the elab test: a false `<=` witness under fuel_monotone, the anti-monotone claim (the add IR answering below its bound), and a wrong-result equiv.

  DEFERRED: nothing from items 3-4. What this round did NOT do -- refinement between two *semantically different* IRs for the same function (the chain here is one IR reached through zero, one and two LetCall wrappers, which is the honest small version of the stress test; relating a theta-loop add to a recursive-Apply add wants an env-independence lemma and is a round of its own), and the exists-closure, which is [[surface-existential]].

- 2026-08-01: **`converges` reaches its §6 shape.** [[surface-existential]]
  route 1 landed (value parameters on `record`,
  `docs/surface-value-parameters.md`), so the design's own definition is now
  writable and is written:

  ```heather
  record Converges(p: Prog, env: Val, ir: Ir, vs: Val) {
      n: Nat,
      h: eval(n, p)(env, ir) = Out(vs),
  }
  ```

  The bound is genuinely hidden, which is the part the computed-bound form
  could only approximate. `refines` in the ∃-shape drops its fuel map
  entirely — `refines_trans_conv` is implication chaining, no `b1`/`b2`, no
  bound arithmetic in the statement — and `add_converges` /
  `add_converges_through_calls` export the certificate in the shape a
  `Compile` instance actually wants.

  **Additive, not a rewrite.** Every bounded theorem stays exactly as it was,
  and `refines_of_bounded` is the ∃-closure *proved* in one line rather than
  asserted in a note — which is what makes "nothing re-proves" a fact about
  the file instead of a claim about the future. Doc §13 note 7 amended
  accordingly; the second half of that note (`refines` cannot be *named*,
  because a `fn` body is an expression and `->` is not one) survives and is
  [[type-definitions]]'s.

  Also landed: `BindInv`, the inversion record for `k_bind`, proved once by
  `k_bind_inv` and consumed by `k_bind_mono` through a destructuring `let`. It
  **retires three of `step_mono`'s four convoy motives** — measured, release,
  everything else held identical, **38.5s → 33.7s (−12.6%)**. The fourth
  (`LoopIter`) scrutinizes through `k_iter` rather than `k_bind` and keeps the
  remember idiom; giving it its own inversion record is the same move again
  and is left for a second consumer.

  Check time for the file: **27.5s → 33.7s** release. The +6.2s is the added
  surface (2 records, 9 theorems), against −4.9s given back by the convoy
  retirement. Still inside the test binary's 300 CPU-s debug rail; the header
  of `crates/elab/tests/ir_v1.rs` carries the updated budget note, and it is
  the thing to weigh before the next `step_mono`-shaped theorem.
- 2026-08-01: §6's interface is now FULLY NAMEABLE, and doc §13 note 7 is fully spent. [[type-definitions]] landed route 2 (types are expressions), so `fn Refines(p1: Prog, i1: Ir, p2: Prog, i2: Ir) -> Type { (env: Val) -> (vs: Val) -> Converges(p1, env, i1, vs) -> Converges(p2, env, i2, vs) }` is a declaration in lib/certgen/ir_v1.hthr and refines_refl_conv/refines_trans_conv/refines_of_bounded are stated through it. Note 7's two reasons are now BOTH retired — the first by value parameters on 2026-08-01 morning (Converges), the second by this round. docs/ir-simulate-design.md §13 note 7 carries the amendment. Side effect worth having: the file got FASTER, 35.96s -> 32.90s release, since the shape is elaborated once instead of six times.
- 2026-08-01: **Closing: §11 is fully discharged and re-verified today.** Items 1/2/6 landed 2026-07-31; items 3–4 landed 2026-07-31 with their statement-shape deviations since retired (Converges in the ∃-shape 2026-08-01 morning, Refines named 2026-08-01); item 5 landed as conv/simulate-payload + conv/simulate-depth and its re-aimed nesting obligation was retired with its reason recorded (§11 item 5, §13 note 6). Verified before closing: crates/elab/tests/ir_v1.rs green under scripts/test (2 passed, 198s debug against the 300 CPU-s rail) and the release CLI check ok at 33.7s. Residue re-homed rather than left here: the semantically-different-IRs stress test is [[cross-ir-refinement]] (filed today); §12's open questions already carry their homes in the doc (Prim/datarepr → [[datarepr-separation]], CallCtx descriptor → [[compile-typeclass-design]], Apply result arity → decided by v1 at arity-per-Function with Gamma/Theta the multi-slot binders, embeddings' eventual home → [[generators-in-the-language]]). docs/ir-simulate-design.md stays the specification lib/certgen/ir_v1.hthr is checked against; [[compile-typeclass-design]] and [[end-to-end-compile-instance]] unblock.
