---
title: Emitted annotations no registered code can name: fn-typed-parameter Apps, monomorphized and quoted Wf copies
status: open
labels: [elaboration,performance]
created: 2026-08-13
updated: 2026-08-13
---

The emitted-mass residual of [[wf-shape-annotation-slots]]'s round (docs/wf-shape-code-design.md §7), promoted out of that closing issue's log so it keeps a live home. Two families of emitted `Type::Wf` occurrences survive both spelling rounds because no registered definition names them:

1. **An `App`'s `dom`/`cod` at a function-typed parameter** (`ev: Val -> Ir -> Res`): the annotation is copied from the binder's type during elaboration, not from a callee's Psi statement, so the statement-respell cascade cannot reach it. A handful of occurrences per declaration — small, but named and measured.
2. **`Type::Wf` occurrences that are not any declaration's registered lowering**: monomorphized instantiations (the `Box<T>`-style per-instantiation copies — registration is closed-only by design, [[wf-field-conversion-cost]]) and copies quoted inside a code literal (`⌜⟦D⟧⌝`), where a reference cannot stand because the quote is syntax. This includes open instantiations of a parameterized or value-indexed record: there is a declaration to name, but today's `TyCode` registration cannot abstract over the instance telescope.

Fix shapes, if a round takes one: (1) is a use-site respell at the App-annotation emission (the machinery exists: `respell_ty_deep`); (2) is harder — per-instantiation registration keyed by the monomorphized type, or accepting it as the boundary of the scheme.

## When

Triggered: the next time emitted node mass matters on a workload where the per-slot counters attribute the residual to these families — one deliberate round, per the accumulator discipline. Re-run the counters first; both families were a minority of mass when filed (2026-08-13).

## Log

- 2026-08-13: A NEGATIVE FOR THIS ISSUE'S TRIGGER, from the certgen family's post-evaluation attribution round ([[certgen-harness-cost]] owns the round and its numbers). The trigger says "the next time emitted node mass matters on a workload where the per-slot counters attribute the residual to these families" -- so, recorded: on today's certgen workload, **emitted node mass does not matter**, and family (1) in particular is not what is being paid.

The measurement (rendered-Psi bytes added per declaration, against that declaration's wall, 2026-08-13): `ta_inr` in lib/certgen_code.hthr adds **289 kB** of Psi and checks in **117 ms**; `ta_app` adds 246 kB and checks in 96 ms; `k_bind_mono` in lib/ir_v1.hthr adds **129 kB** and checks in **2,430 ms**. That is a ~150x spread in time-per-emitted-byte between a `refl` pin and a transport lemma, in the direction opposite to mass.

`k_bind_mono` is the interesting case for this issue specifically, because it is exactly family (1)'s shape -- three function-typed parameters (`ev1`, `ev2`, `hyp: (e, i, w) -> ev1(e,i) = Out(w) -> ...`), so its `App` `dom`/`cod` annotations are the unnameable copies this issue owns, and 129 kB for thirteen lines is presumably largely them. At `ta_inr`'s rate that mass would cost ~50 ms; it costs 2.43 s, of which `conv_type` is 2.05 s in a long tail of individually expensive comparisons ([[conversion-cost-at-large-values]], logged today). So the mass is real and this issue's family (1) is confirmed present at a named declaration -- it is simply not the cost there, and a use-site respell at the App-annotation emission would not move that workload. Re-run the counters before spending a round, as this issue already says; this entry is the denominator for the next person who does.

- 2026-08-25: **Trigger fired for family (2)** in
  [[ir-pass-probe-elaboration-cost]]. `IrPassLawsProbe<M>(R, alg)` is a
  parameterized and value-indexed proof record instantiated openly at
  `M = Ir`; its exact rendered type is about 1.00 MB, and record/law bodies
  carrying its construction and projections render at 9.92--32.28 MB each.
  Dependent matches directly on `Ir` contribute another 21.71--31.45 MB per
  declaration. Per-gate conversion, typing, and evaluator counts track those
  sizes linearly, and the standalone target spends about 36 seconds checking
  them.

  This is the positive counterpart to the 2026-08-13 certgen negative: emitted
  annotation mass is the wall here. Local `let`, theorem opacity, proof
  splitting, and an evaluator zero-step shortcut were all measured and
  rejected; none names the open instantiated type. The next design should
  weigh a telescope-abstracted `D#tycode` (including value parameters) or an
  equivalent local/open type-sharing representation, then respell the record
  literal/projection and Wf-match annotation sites. It must retain inline
  copies at structural readers and the wrong-global/look-alike negatives of
  the closed-family code-definition rounds.
