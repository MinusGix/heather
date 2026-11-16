---
title: grind: constructor injectivity and disjointness, disequalities, False goals
status: closed
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-05
---

Round 3 of [[grind-port]] (`docs/tactics/grind-design.md` §6): what constructors
and disequalities say.

- Injectivity: `Cons(a, as)` and `Cons(b, bs)` in one class gives `a = b`
  and `as = bs` (the constructor's projections, or the derived
  `T::cong_C`'s converse).
- Disjointness: two different constructors of one type in one class is a
  contradiction, which proves any goal.
- `a ≠ b` among the locals, and a goal `False` or `a ≠ b`: a contradiction
  is two members of a class that a disequality separates.
- The stuck state names the disequalities read.

Round 1 reads a constructor value as its constructor's function applied to
its fields (congruence only), and refuses goals other than equations.

Done when `Cons(a, as) = Cons(b, bs) → a = b`, `Nil = Cons(x, xs) → P`,
and `f(a) ≠ f(b) → a ≠ b` close by `grind()`.

## What it assumes from elsewhere
- **[[grind-port]]** owns the graph. Assumed here: only that classes and
  their members can be read.

## Log

- 2026-11-05: Round 3 done (docs/tactics/grind-design.md §14, host design §25). Injectivity (`Inj`) and disjointness (`Absurd`) as host requests running the surface builders; disequalities read (`≠`, `→ False`, `Not`); goals opened under `→`/`Not` and proved from a contradiction when no equation; `Nat`'s `Succ` as a constructor (`grind::succ_fn`, `grind::succ_inj`); `Spine` contracts a head β-redex; a `KOther` leaf read once in head normal form; and, once the graph as written is stuck, every fact side's head normal form (constructor values as nodes, stuck forms compared by `Defeq`, never nodes; injectivity/disjointness asked about the sides as written). Host: `Whnf` contracts pair projections; `View` sees an applied stuck `match` as `HMatch`. Converted: `round_real`'s disjointness arms and `linux_world_co`'s six `pass_reading_at` steps. Minus decided any std module grind's imports allow may import it; conversions in modules on hand-written closure lists (compile-x86's bundle, the Rust tests' lists) were taken back for the closure's cold cost ([[grind-closure-cost]], §14.5). All three done criteria are probes. Left: [[grind-reduct-fields]].
