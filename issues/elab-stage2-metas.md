---
title: "Elaborator stage 2: metas-as-Psi-globals + level inference"
status: open
labels: [frontend,elaboration]
created: 2026-07-23
updated: 2026-07-23
---

Stage 2 of [[elaborator-design]] (architecture decided there; this is the
work item). Goal, concretely benchmarked: the stage-1 Nat suite
(crates/elab/tests/nat_suite.rs) drops its explicit `as z -> M` motives and
lemma-endpoint arguments — `sym(add(n,0), n, add_zero(n))` becomes
`sym(add_zero(n))` (or `add_zero(n).sym()` with [[surface-operators]]) —
with no kernel change.

Work items:

- **Meta representation**: fresh `u : Trm(Γ ⊢ T @ l)` Ψ-bindings appended
  to an elaboration-local Ψ-extension; occurrences `u^δ`; solutions applied
  by global substitution σ. Zonking = applying the accumulated σ before the
  final kernel check (the kernel never sees an unsolved meta).
- **Unifier**: comparison loop mirroring conv.rs structure (whnf via
  kernel, congruence cases per former), producing constraints on
  meta-headed neutrals instead of NotConvertible. Pattern-condition check =
  "δ is a variable renaming". Postponement for non-patterns; fail with the
  constraint printed, no proof search.
- **Level metas**: fresh L-vars + unification over count/adjust normal
  forms (Level::normalize is the oracle). No generalization yet (stage-1
  programs are level-0; `ΠΠ` generalization is layer-m, later).
- **Motive synthesis**: `match e` with `e` a variable in checking position
  abstracts the scrutinee from the expected type (the clear-and-generalize
  move stage 1 punted on); explicit `as` stays as the escape hatch.
- **Implicit lemma endpoints**: theorem parameters inferable from later
  ones (the `a b : Nat` of `sym` from `p : a == b`) become implicit at call
  sites — needs a surface marker or inference-by-default policy; decide
  against [[surface-syntax]] taste (lean: trailing explicit proof args,
  earlier endpoints implicit by default, `@name` for the fully explicit
  form).

Acceptance: annotation-free Nat suite green; stage-1 explicit forms still
accepted (they are the fallback the sketches promise).

## Log

- 2026-07-23: Opened as part of the granular issue split after stage 1.
