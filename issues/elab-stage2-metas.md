---
title: "Elaborator stage 2: metas-as-Psi-globals + level inference"
status: closed
labels: [frontend,elaboration]
created: 2026-07-23
updated: 2026-07-24
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
- 2026-07-24: Stage 2 landed (both ergonomics). Motive synthesis: motive-less `match` in checking position abstracts a *variable* scrutinee out of the expected type via a pure kernel substitution (shift_local + an apply_local swap `Var(scrut+1)->z`); non-variable scrutinees fall back to the non-dependent motive. No metas. Implicit endpoints: `{}`-implicit params (surface) + `@f(...)` explicit-override; each implicit becomes a fresh metavariable represented as an *innermost* Psi-binding `?m^{id_G}` (GlobalTm at index <n, committed globals shifted up by n), solutions recorded by a best-effort unifier (Id/Nat congruence, Miller-pattern meta solve = subject verbatim since delta is identity on G), whole meta block discharged by one apply_global sigma that also renumbers committed globals back down. Kernel re-checks the zonked term, so a mis-solved meta is a rejection not unsoundness. Acceptance MET: crates/elab/tests/implicit_args.rs (annotation-free Nat suite, 7 Psi-globals) + motive_synth.rs green; stage-1 explicit forms kept green in nat_suite.rs via `@`. Deferred (not needed by the level-0 suite, file as follow-up): level metas/inference; general delta inversion + constraint postponement (current unifier never blocks — unsolved metas error, wrong solutions are kernel-caught).
