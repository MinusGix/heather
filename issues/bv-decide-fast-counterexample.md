---
title: bv_decide: try random values before the solver
status: open
labels: [bitvec,solver,tactics,feature]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

A false claim pays for evaluating its clauses and running the solver before it fails. The host could first evaluate the predicate at a few random and boundary values (0, all ones, the sign bit) and report a counterexample at once; only claims that survive go to the solver.

Parent: [[lrat-certified-bitvector-decision]].
