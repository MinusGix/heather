---
title: grind: constructor injectivity and disjointness, disequalities, False goals
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Round 3 of [[grind-port]] (`docs/grind-design.md` §6): what constructors
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
