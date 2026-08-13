---
title: Emitted annotations no registered code can name: fn-typed-parameter Apps, monomorphized and quoted Wf copies
status: open
labels: [elaboration,performance]
created: 2026-08-13
updated: 2026-08-13
---

The emitted-mass residual of [[wf-shape-annotation-slots]]'s round (docs/wf-shape-code-design.md §7), promoted out of that closing issue's log so it keeps a live home. Two families of emitted `Type::Wf` occurrences survive both spelling rounds because no registered definition names them:

1. **An `App`'s `dom`/`cod` at a function-typed parameter** (`ev: Val -> Ir -> Res`): the annotation is copied from the binder's type during elaboration, not from a callee's Psi statement, so the statement-respell cascade cannot reach it. A handful of occurrences per declaration — small, but named and measured.
2. **`Type::Wf` occurrences that are not any declaration's registered lowering**: monomorphized instantiations (the `Box<T>`-style per-instantiation copies — registration is closed-only by design, [[wf-field-conversion-cost]]) and copies quoted inside a code literal (`⌜⟦D⟧⌝`), where a reference cannot stand because the quote is syntax.

Fix shapes, if a round takes one: (1) is a use-site respell at the App-annotation emission (the machinery exists: `respell_ty_deep`); (2) is harder — per-instantiation registration keyed by the monomorphized type, or accepting it as the boundary of the scheme.

## When

Triggered: the next time emitted node mass matters on a workload where the per-slot counters attribute the residual to these families — one deliberate round, per the accumulator discipline. Re-run the counters first; both families were a minority of mass when filed (2026-08-13).
