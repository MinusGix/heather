---
title: A merged call through a definition declared at a parent class panics the kernel's substitution
status: closed
labels: [elaborator, kernel-panic, classes]
area: language
milestone: [none]
created: 2026-11-07
updated: 2026-11-07
---

Calling a theorem whose result type is a definition that unfolds to a Π,
with the Π's arguments merged into the theorem's own argument list, panics
when the definition was declared in a parent class's section and the call
sits in a child class's section:

```
section<K: OrderedField(≈, <, <=, +, *)> {
fn Ub(S: K → Type, b: K) → Type { (x: K) → S(x) → x <= b }
}
section<K: CauchyComplete(≈, <, <=, +, *)> {
fn Eb(xs: Nat → K, y: K) → Type { ∃ N: Nat, (n: Nat) → Nat::Le(N, n) → y <= xs(n) }
theorem ub_at(xs: Nat → K, b: K, h: Ub(λ (y: K) => Eb(xs, y), b)): Ub(λ (y: K) => Eb(xs, y), b) { h }
theorem merged(xs: Nat → K, b: K, h: Ub(λ (y: K) => Eb(xs, y), b), y: K, sy: Eb(xs, y)): y <= b {
    ub_at(xs, b, h, y, sy)
}
}
```

(with the imports of lib/std/analysis/sequence.hthr plus `sequence`.) The
check panics with `kernel invariant violated: local variable 14 escapes the
substitution's target entries (variables cannot address a context-variable
base)`, under `apply_implicit_planned` → `Elaborator::whnf` →
`whnf_type_delta` → `SubstLocal`. The curried form `ub_at(xs, b, h)(y, sy)`
and a `let` of the partial call both check, and the same declarations all in
one `OrderedField` section check merged. So the over-application path
δ-unfolds the result type under a context whose upcast prefix (the
`CauchyComplete` dictionary read as an `OrderedField`) the substitution does
not cover. It predates #462 (the per-prefix upcast minting): master at
53c1f46 panics too, at variable 22.

Two defects: the panic itself (an elaborator route handing the kernel an
open term), and the `consecutive calls … can use one argument list` lint,
which recommends exactly the form that panics.

Hit in lib/std/analysis/supremum.hthr (`OrderComplete::below_located`
binds `bound_at`'s result with `let` to avoid it;
docs/library/sequences-and-completeness.md §4).

## Log

- 2026-11-07: Filed from the located-suprema round ([[order-completeness-located-sup]]).
- 2026-11-07: Fixed. Root cause and why it was a panic:

  **Not an open term — a term read in the wrong global world.** An
  implicit application works in a *scratch world*: its `n` metavariables are
  globals `0..n` and every committed global is shifted up by `n`
  (`application.rs`). The type at the panic was locally well-scoped (its
  free-variable bound was exactly `|Γ|`), but the spill loop — arguments past
  the declared spine, applied to the callee's result while an implicit is
  still open — asked `whnf_for_application`, i.e. the committed-world
  `Elaborator::whnf`, to reduce it. So δ read every global `n` bindings too
  deep: `Ub`, two deep in Ψ, appeared as `u9` with `n = 7`, and the
  definition nine deep was unfolded instead, its body (scoped in its own,
  longer context) substituted by this occurrence's twelve-payload
  substitution. Local variable 14 had no payload: the assertion.

  Only through an upcast because the spill loop runs only while an implicit
  is unsolved: from a child class's section the parent-class definition's
  dictionary slot is a solver slot (resolved after the arguments), so it is
  still open when the trailing `y, sy` arrive. In one section the slot is
  solved first, the loop never runs, and the spill is applied after
  zonking, in the committed world. Any time the misread global happened to
  be a declaration rather than a definition, the δ step was simply stuck,
  the loop gave up, and the call checked by luck.

  **Why the kernel aborted rather than refused.** Typing refuses such an
  occurrence (`subst_ck`: `δ` must have one payload per entry of the
  definition's context, else `SubstMismatch`). Reduction is not a judgement
  and is documented to reduce ill-typed input to a stuck form, but its δ
  rule did not check that side condition before substituting the body, and
  the substitution's scoping assertion is the only guard below it. The
  elaborator runs the reducer on terms no judgement has seen, so the
  precondition was the elaborator's to keep, and the first one that broke
  it found the assertion. (The value machine had the same gap silently: it
  read the uncovered entries as base variables.)

  Fixes, either alone sufficient for the reproduction:
  - elaborator: `whnf_for_application` takes the world's width, and
    `Elaborator::whnf_in` reduces a scratch-world type in the semantic world
    extended by `n` body-less stand-ins (reduction reads only bodies), with
    the scratch-aware `unspell_here_in`. Also used by
    `infer_bare_polymorphic_argument`'s inner scratch world, which had the
    same shape. The spill loop now *can* see through such a result type, so
    an argument that does not infer there (`Inl(…)` at `¬ Apart(…)`) stops the
    teaching and is checked after zonking, instead of refusing the call.
  - kernel: `Defs::fits` — δ (plain, withheld, sealed; reducer and value
    machine) unfolds an occurrence only when its substitution fits the
    definition's context; otherwise it is stuck, and typing refuses it.
    `crates/kernel/tests/definitions.rs`
    `an_occurrence_that_does_not_fit_its_definition_is_stuck`.

  The lint is now right: `supremum.hthr`'s `below_located` uses the merged
  form again, and `lib/_tests/std/analysis/supremum_tests.hthr` keeps the
  reproduction with a wrong-argument negative control.
