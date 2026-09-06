---
title: Unfolding equations for the members of a mutual-recursion group
status: open
labels: [frontend,elaboration,proofs]
created: 2026-09-05
updated: 2026-09-05
---



Residue of [[mutual-recursion-declarations]] (landed 2026-09-05,
docs/mutual-recursion-design.md §6). A group member gets no `f_unfold`; a
citation reports the deferral through `unfold_refusals`. What it needs, per
§6: `g#ext` with one hypothesis per product component, and bound
irrelevance for `f#grp_rec` as a tuple-level equality (`pair::pair_ext`
applied N-1 times, all N `#ext`s in the `Succ`/`Succ` case). The customer
does not pay yet: the parser's bodies are outside the companion walk's
fragment anyway ([[unfolding-computed-scrutinee]], and a `let` whose
right-hand side holds a call). A neutral-argument *equation* about a member
(`parse_atom(Cons(t, rest)) = parse_expr(rest)`) is what this would supply.

## What it assumes from elsewhere
- **[[decreases-unfolding-equations]]** owns the singleton companions.
  Assumed here: only their shape (`#ext`/`#irrel`/`_unfold`).
