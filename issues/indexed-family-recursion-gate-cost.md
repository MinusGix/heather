---
title: Recursion over typed-syntax and function-field families is superlinear in constructors, nearly all in the gate
status: open
labels: [kernel,elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-26
updated: 2026-10-26
---

Found by the intricate-inductive bench families
([[intricate-inductive-bench-families]], `inductive/typed-syntax` and
`inductive/function-fields`). Both declare cheaply; a structural `size`
over them and a one-step `refl` unfolding are where the time goes, and it is
90 to 98% kernel gate.

**Function fields** (`IWf` on `W`, [[indexed-infinitary-families]]): `Tr :
(n: Nat) -> Type` with `Lf : Tr(0)` and `n` constructors `Brᵢ(n: Nat, k: (y:
Nat) -> Tr(n)) : Tr(Succ(n))`, a `size` through `k(0)`, a closed and an open
`refl`. `heather check --timings`, release, width one:

| ctors | `size` total / gate | queries | closed `refl` | open `refl` |
|---|---|---|---|---|
| 4 | — | — | — | — (0.28 s whole file) |
| 8 | 509 / 498 ms | 664,979 | 215 ms | 99 ms |
| 16 | 5,556 / 5,515 ms | 7,158,355 | 715 ms | 811 ms |

×11 from 8 to 16 constructors (queries ×10.8), about the cube. **Control:**
the same family with `k: Tr(n)` (no function field) at 16 constructors is
84 ms for `size` and 10 to 19 ms per `refl`, so it is the `W` route, ×60.

**Typed syntax**: `Tm(J(Γ, A))` — variables, weakening, λ, application and
`n − 4` binary operators, indexed by a declared judgment type (one index per
family today, `docs/inductive-indexed-lowering.md` §8.4), `size` at the
rebound judgment, an open and a closed `refl`:

| ctors | `size` total / gate | queries | open `refl` | closed `refl` |
|---|---|---|---|---|
| 5 | 247 / 225 ms | 229,378 | 361 ms | 250 ms |
| 12 | 4,135 / 3,932 ms | 4,105,404 | 2,396 ms | 1,483 ms |

The constant is the striking part: a one-step `refl` of a three-node closed
term costs a quarter of a second at five constructors and a second and a
half at twelve, so a theorem file over a real object language pays seconds
per lemma statement.

Not attributed. The two share a shape — an `IWf` whose `ok`/index
predicates and motives are re-walked by conversion per constructor — and
[[elab-whnf-family-transport-cost]] is the last round that moved this layer.

Acceptance: both families' slopes fall towards 1, re-recorded from below,
and the per-`refl` constant at twelve constructors drops by an order of
magnitude.

## What it assumes from elsewhere

- **[[indexed-infinitary-families]]** owns the `IWf`-on-`W` encoding. Assumed
  here: only that a function child is checked through `ok`.
- **[[indexed-families]]** owns the routes and the one-index limit (§8.4).
  Assumed here: only that `Tm` takes the `IWf` route, which the bench fixture
  asserts.
