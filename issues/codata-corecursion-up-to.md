---
title: Corecursion up to friendly functions
status: open
labels: [codata,coinduction,elaborator,design]
area: interaction-trees
created: 2026-11-01
updated: 2026-11-01
---

A corecursive call must be a child of the constructor the step returns, or
of constructors nested inside it (`docs/codata-elaborator-design.md` §5.2,
§5.4). A call inside any other tree is refused with this issue:

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
