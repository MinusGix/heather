---
title: A monotonicity tactic that reduces an inequality to its parts (gcongr)
status: open
labels: [tactics,reals]
area: tactics
milestone: [tac-general]
created: 2026-10-27
updated: 2026-10-27
---

Most of a real-number proof is monotonicity plumbing. In
`lib/std/num/float/series.hthr` a bound such as `t·h + t·h <= t·(h + h)`
under `|r| <= h` is written as
`Rat::add_le_mono(Rat::mul_le_mono_l(h1, t.abs_nonneg()), …)`: the user spells
the goal's shape a second time as a tree of `*_mono` lemmas and discharges
each nonnegativity side condition by hand.

Wanted: a `gcongr`-style tactic (Lean's `gcongr`). Given a goal `f(a₁, …) R
f(b₁, …)`, it matches both sides against one pattern, finds the `@[mono]`
lemma for each operation and position, and reduces the goal to `aᵢ R bᵢ` for
each place where the sides differ. Each reduced goal is closed by an
assumption or a given term, or left open. Side conditions (`0 <= z`) go to a
small positivity search over `abs_nonneg`, `inv_succ_pos`, numerals and
hypotheses.

Scope:

- a `mono` registry over the existing lemmas (`add_le_mono`, `mul_le_mono_l/r`,
  `neg_le`, `sub_le_sub_l/r`, `inv_le_inv`, `npow` monotonicity), at `Rat`,
  `CReal`, `Int` and `Nat` alike, through their classes where one exists;
- the pattern found by anti-unifying the two sides
  (`congruence-by-anti-unification` has the machinery);
- `calc` steps can use it as their justification (`<= … := mono(h)`).

## What it assumes from elsewhere
- **[[congruence-by-anti-unification]]**: the shared pattern of the two sides.
- **[[ordered-algebra-api]]**: where the monotonicity laws live as class laws.
