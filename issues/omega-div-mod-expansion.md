---
title: Extend Omega reflection through division, modulus, and divisibility
status: open
labels: [proofs,elaboration,metaprogramming,stdlib,arithmetic]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-26
updated: 2026-08-27
---

Extend Heather's Omega frontend through division and remainder by nonzero
literal constants and through divisibility propositions. This is an expansion
of the linear solver, not part of its core elimination algorithm.

Follow Lean's scheme: reify `x / k` as a fresh integer atom `q`, add the
Euclidean interval `0 <= x - k*q <= k - 1`, reify `x % k` as `x - k*q`, and
translate literal divisibility to a remainder equality. Negative divisors and
zero require explicit, tested semantics rather than incidental reduction.

The standard library first needs executable `Nat`/`Int` division and modulus
and the complete correspondence kit consumed by the reconstructor. The
operational definitions and laws are owned here because the frontend is not
useful until computation and certificates agree. Solver-side auxiliary atoms
must reuse the derivation DAG and report their defining facts.

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
- 2026-08-27: Landed the operational and law foundation without fuel or a
  division-specific termination rule. `Nat.divmod` scans the numerator by
  immediate structural recursion and shares quotient/remainder state; its
  kernel-checked specification proves reconstruction and the positive-divisor
  remainder bound. `Int.divmod` uses explicit Euclidean semantics in all four
  sign quadrants: the remainder is nonnegative and below `abs(divisor)`, a
  negative divisor only negates the quotient, and at zero the quotient is zero
  and remainder is the dividend. Open reconstruction and bound laws are
  kernel-checked. General `decreases` remains independently owned by
  [[termination-measures]] rather than acquiring division-shaped machinery.
  Remaining work here is existential divisibility and frontend auxiliary atoms.
- 2026-08-27: Landed the first frontend auxiliary-atom slice for `Int`
  division and modulus by positive literal divisors. A quotient is one shared
  opaque atom with certified Euclidean lower and strict upper constraints;
  modulus normalizes to `x - (x / k) * k` and reuses that same atom. The
  defining facts are ordinary assumptions in the existing derivation DAG and
  their supporting proofs are kernel-checked `int::div_mul_add_mod`,
  `int::mod_nonneg`, and `int::mod_lt_abs` consequences. End-to-end rails cover
  both quotient bounds, both remainder bounds, atom sharing, and refusal of a
  false remainder mutation. Negative and zero literal divisors, `Nat`, and
  existential divisibility remain explicit follow-ups.
- 2026-08-27: Generalized the `Int` frontend to every literal divisor. For a
  negative divisor, quotient constraints retain its signed coefficient while
  the strict Euclidean width uses its absolute value; constructor-specific
  nonzero proofs keep this entirely certified. Division and modulus by zero
  normalize through the library's explicit total semantics and introduce no
  quotient atom. Rails cover negative quotient and remainder bounds plus open
  zero-divisor identities. Remaining frontend work is `Nat` and divisibility.
- 2026-08-27: Extended the frontend through `Nat` quotient and remainder by
  literal divisors, including the library's total zero-divisor semantics.
  Natural quotient atoms share the same certified embedding used by ordinary
  natural arithmetic, with native lower/upper division laws and nonnegativity
  available to reconstruction. Added `nat::Divides` and `int::Divides` as
  definitionally zero-remainder propositions; this is extensionally the usual
  existential notion under the executable Euclidean laws, while letting both
  positive and negated uses enter Omega without synthesizing quotient
  witnesses. End-to-end rails cover natural quotient/remainder bounds,
  divisibility, disequality splitting, and rejection of false divisibility.
  The remaining acceptance item is an explicit large-literal scaling rail.
