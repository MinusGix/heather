---
title: "Kleene algebra with tests: the class, the relational model, and equivalence of structured control flow"
status: open
labels: [stdlib,mathematics,algebra,automata,passes]
area: mathematics
milestone: [math-formal-languages,hih-passes]
blocked-by: [regular-languages-by-derivatives]
created: 2026-11-10
updated: 2026-11-10
---

Area 5 of the 2026-11-10 ranking, second piece. Take it when a
control-flow pass is the next pass to prove.

Kleene algebra with tests is the equational theory of sequence, choice
and iteration with Boolean guards. `StructuredRegion` (a tree of
sequence, branch and loop) is that signature, and binary relations with
`Star` (`lib/std/relation/transition.hthr`) are a model.

## Scope

- `KleeneAlgebra` over the semiring classes (idempotent `+`, `star` with
  the induction axioms) and `Kat` with an embedded Boolean algebra of
  tests; the derived laws (sliding, denesting, bisimulation).
- Models: relations on a state type with `Star`; regular languages
  ([[regular-languages-by-derivatives]]).
- An interpretation of a structured region's control skeleton as a KAT
  term whose relational meaning is the region's step relation, so that a
  KAT equation is a statement about runs.
- A decision procedure for KAT equations by automata, reflective, as
  the tactic; until then, the laws as a `simp` set ([[simp-tactic]]).

## Done when

One control-flow rewrite over `StructuredRegion` (loop unrolling, or
removing a branch whose test a fact decides) is proved by a KAT equation
instead of by induction on runs.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** (closed) owns `Star`.
- **[[function-ir-verified-lowering]]** owns the region semantics.
