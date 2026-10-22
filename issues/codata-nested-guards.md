---
title: Corecursive calls nested under a second constructor
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-10-22
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
