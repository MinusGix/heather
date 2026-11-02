---
title: Corecursion up to friendly functions
status: closed
labels: [codata,coinduction,elaborator,design]
area: interaction-trees
created: 2026-11-01
updated: 2026-11-02
---

A corecursive call must be a child of the constructor the step returns, or
of constructors nested inside it (`docs/codata-elaborator-design.md` §5.2,
§5.4). A call inside any other tree was refused with this issue:

```
fn bad(n: Nat) → Stream { SCons(n, tl(SCons(n, bad(n)))) }
fn mul(f: Series, g: Series) → Series { SCons(hd(f) * hd(g), add(mul(tl(f), g), mul(f, tl(g)))) }
```

That is corecursion *up to* a function: `add` here, `bind` or `trans` in
an up-to proof. It is sound when the function is "friendly", that is, it
consumes at most one layer of each argument to produce one layer of
output (Blanchette, Bouzy, Lochbihler, Popescu and Traytel, *Friends with
Benefits*, 2017). Customers:

- the Leibniz product of formal power series as codata
  (`issues/formal-power-series.md`, `docs/analysis-foundations-design.md`);
- up-to techniques for `Bisim`/`Eutt` (a self-call under `trans` or
  `bind`, `docs/coitree-design.md` §7.6);
- a direct coinductive `rec`, whose non-tail call sits under `bind`
  (`docs/partial-functions-design.md`; `CoTree::rec` works around it with
  `interp_mrec`).

## Design questions

- Which functions count as friendly, and how a function proves it: a
  syntactic check on its own definition (a corecursive function whose calls
  are all guarded and whose arguments are consumed one layer at a time), or
  a registered friend with a proof obligation.
- The carrier: the free algebra of the friends over seeds, as in Isabelle's
  `corec`, which the kernel's `corec` can host with a W-typed (or layered,
  as in §5.4) carrier.
- What `refl` keeps: observations of a corecursion up to `add` compute only
  as far as `add`'s own unfolding does.

## Log
- 2026-11-02: Round 1 done (`docs/codata-elaborator-design.md` §5.5). The design questions, answered: (1) friends are decided **syntactically on the friend's own definition**, with no registration and no proof obligation: the friend's body is re-elaborated ("friend mode") over the calling definition's carrier, where a codata parameter may only be a `match` scrutinee (one layer), an argument of the friend's own guarded call, a child, or the whole result; the kernel checks the outcome as part of the `corec`. (2) The carrier is the **free algebra** of the friends over seeds and existing trees, a finitary `Wf` tree `C = Wf(a : X + ⟦D⟧ + A₁ + … + A_m). n(a)`, and the step is structural recursion on it (`elim_Wf`, a convoy over the shape): a friend node's step reads its arguments' first nodes from the recursion's `ih`, so productivity is the `corec`'s and termination the `Wf` recursion's. (3) `refl` keeps observations as far as the friend's own unfolding: `nth(smul(from(1), from(1)), 2) = 14` and the neutral `hd(tl(smul(f, g)))`; a tree under a friend is not convertible with the friend applied to the trees. Tests in `crates/elab/tests/codata.rs` (Hurwitz product up to stream addition, `scale` with a data argument, colist `append` returning its argument, a friend over function children, a friend from another module's image, controls including `skip`, which reads two layers and would make its caller unproductive). What round 1 does not cover (indexed codata for `Bisim`/`Eutt` up-to, polymorphic friends, `bind`-shaped friends for a direct coinductive `rec`, friends calling friends, nesting beside friends) is [[codata-up-to-friends-round-2]].
