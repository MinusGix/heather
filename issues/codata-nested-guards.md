---
title: Corecursive calls nested under a second constructor
status: closed
labels: [codata,coinduction,elaborator]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-11-01
---

A corecursive call must be a *direct* child of the constructor the step
returns (`docs/codata-elaborator-design.md` §5.2). A call nested under a
second constructor is refused:

```
fn echo() -> Tree { Vis(Ask, λ n => Tau(echo())) }
```

The workaround is to write the pending constructor as a seed state
(`echo(w: Phase)` with `Waiting` and `Ticking`). The general fix is the one
`docs/kernel-coinduction-design.md` §6 sketches: the elaborator generates
the carrier, as the varying parameters plus one state per constructor that
is nested above a call (`X + X_{Tau} + …`), and each state's step emits that
constructor. `bind` and `iter` in the coinductive tree library want it,
since `iter`'s `Continue` emits a `Tau` before the next seed.

Design points:
- The generated states carry the free variables the nested constructor's
  arguments mention, like a closure conversion of the guard context.
- Observations still compute by β under `out`, one per constructor layer,
  so `refl` theorems keep working.
- Productivity stays syntactic: every path from the root to a self-call
  passes through at least one constructor.

## Log
- 2026-11-01: Done for unindexed codata (`docs/codata-elaborator-design.md` §5.4). The carrier grows one pending-node layer per extra constructor, `C₀ = X`, `C_{j+1} = X + F(C_j)`, counted on the surface before the body is elaborated. A nested constructor is stored as a value of the layer below (`inl(inr(node))`), so nothing is closure-converted: the node holds the variables it mentions as ordinary subterms. The step is `case x { inl(v) ⇒ body; inr(node) ⇒ lift(node) }`, and observations still compute by β one layer at a time (`tl(tl(pairs(n))) = pairs(Succ(Succ(n)))` by `refl`). With no nesting the term is unchanged. Indexed codata is [[codata-nested-guards-indexed]]; a call inside a non-constructor tree (corecursion up to a function) is [[codata-corecursion-up-to]].
