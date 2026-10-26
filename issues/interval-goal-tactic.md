---
title: Reify a rational inequality goal into the interval checker
status: open
labels: [tactics,reals,intervals]
area: tactics
created: 2026-10-26
updated: 2026-10-26
---

`Expr::lt_of_search` (`lib/std/num/float/interval.hthr`, design §16 of
`docs/floating-point-design.md`) proves `a.eval() < b.eval()` from a `True`
verdict, and `Expr::eval` spells each node as the operation itself, so the
goal written directly converts with its `Expr` form. What is left is
writing the `Expr` by hand: a caller restates the goal's expression as a
tree.

A tactic closes that gap: read the goal `L < R` (or `L <= R`) at `Rat`,
build `Expr` trees for `L` and `R` from the operations it recognises
(numerals and `Rat(a, d)` literals, `+`, `-`, unary `-`, `*`, `recip`,
`npow` at a literal exponent), and emit `Expr::lt_of_search(l, r, p, tries,
refl)`. Reification is syntactic only: correctness is the kernel's check
of that term, so a wrong tree is refused, never accepted.

Open choices: the starting precision and number of tries (CoqInterval
starts at 30 bits, which proved 87 of its 101 benchmark goals,
`docs/coq-hardware-floats-survey.md` §6.1); whether an unrecognised
subterm fails the tactic or becomes a variable with a hypothesis-supplied
enclosure (`Expr` has no variables yet); and whether it lives in Heather
(`Tac<A>`) or the host.

## What it assumes from elsewhere
- **[[dyadic-interval-enclosures]]** (closed) owns the checker. Assumed
  here: only `Expr::lt_of_search` / `le_of_search` and that `eval`
  converts to the spelled goal.
