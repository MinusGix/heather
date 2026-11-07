---
title: A merged call through a definition declared at a parent class panics the kernel's substitution
status: open
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
docs/sequences-and-completeness.md §4).

## Log

- 2026-11-07: Filed from the located-suprema round ([[order-completeness-located-sup]]).
