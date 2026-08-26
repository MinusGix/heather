---
title: Extend Omega reflection through division, modulus, and divisibility
status: open
labels: [proofs,elaboration,metaprogramming,stdlib,arithmetic]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-26
updated: 2026-08-26
---

Extend Heather's Omega frontend through division and remainder by nonzero
literal constants and through divisibility propositions. This is an expansion
of the linear solver, not part of its core elimination algorithm.

Follow Lean's scheme: reify `x / k` as a fresh integer atom `q`, add the
Euclidean interval `0 <= x - k*q <= k - 1`, reify `x % k` as `x - k*q`, and
translate literal divisibility to a remainder equality. Negative divisors and
zero require explicit, tested semantics rather than incidental reduction.

The standard library first needs executable `Nat`/`Int` division and modulus,
their termination arguments, and the complete correspondence kit consumed by
the reconstructor. The operational definitions and their termination proof are
owned here because the frontend is not useful until both computation and the
certificate laws agree. Solver-side auxiliary atoms must reuse the derivation
DAG and report their defining facts.

Acceptance includes closed computation, open quotient/remainder bounds,
positive and negated divisibility, mutation rejection, and a rail proving the
frontend does not expand large unary divisions during reflection.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns the linear constraint solver, proof DAG,
  and arithmetic audit state. Assumed here: only the ability to introduce a
  fresh integer atom with certified linear constraints.

## Log

- 2026-08-26: Split from the initial Omega implementation so division's
  executable definitions and termination proofs do not delay useful linear
  arithmetic. Lean's literal-divisor preprocessing remains the reference.
