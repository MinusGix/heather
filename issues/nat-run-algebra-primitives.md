---
title: Run arithmetic as primitives: classify Nat fold algebras semantically, iterate them over programs
status: closed
labels: [kernel,evaluator,representation,performance,nat,design]
created: 2026-09-09
updated: 2026-09-11
---

Lean 4's kernel keeps `Nat` literals as bignums and reduces `Nat.add`, `mul`,
`sub`, `div`, `mod`, `ble`, `beq` on literals in one step, keyed on the
*names* of the structural definitions theorems reason about. Heather's runs
(`Val::NatRun`, [[succinct-inductive-values]]) are halfway there and better
on one axis — a run is `Succ^k(tail)` with an open tail — but the arithmetic
over them is keyed on the *spelling* of a fold's step (`nat_step_successors`,
`nat_step_synchronizes` in `crates/kernel/src/eval.rs`), which
[[kernel-acceleration-policy]] classifies as debt: `mul` is repeated
addition, `sub`/`half` are magnitude-linear, `nat::sub` did not even match
the synchronous spelling, and every new customer wanted its own case.

This issue owns the replacement: **no name and no spelling is recognized.
The step closure is classified by evaluating it** on fresh neutral
variables, and the class is a semantic statement about the algebra that the
run arithmetic then discharges in one program application.

## The classes

A fold `elim_Nat(M; b; s; Succ^c(t))`, with `s` the step closure.

- **Affine.** `s k ih ⇓ T[ih]` where `T` is a tree of pairs whose leaves are
  `Succ^q(ih.π)` (`π` a projection path, `q ≥ 0`) or closed `Nat` literals.
  Then `elim(Succ^c t) = T^c[elim t]`, and `T^c` is computed over the
  program's DAG (binary exponentiation on a run, composition on a compose,
  memoized per node) with `ContextProgram` increments, so nothing overflows:
  saturated runs merge, and compose past `u64`. Covers `add` (`q = 1`),
  `twice`, `λ k ih. ih`, **`mul` by a run** (its step `add(ih, a)` probes to
  `Succ^{|a|}(ih)` through the nested fold — mul of two runs is one
  multiplication), and the course-of-values windows of `half`, `Even`,
  `Odd`, `fib` (a pair tree with a permutation and increments).
- **Synchronous.** `s k ih ⇓ λ m. …` and `(s k ih)(Succ x) ⇓ Succ^q(ih x)`.
  Then `elim(Succ^c t)(Succ^c u) = Succ^{c·q}(elim(t)(u))`: matching prefixes
  cancel (`ContextProgram::cancel_matching_prefix`, already there). Covers
  `Le`, `Lt`, `leb`, `sub`, `min`, `max` — by meaning, so `sub`'s spelling
  no longer matters.
- **Opaque.** Everything else: the ordinary one-step path under fuel.

Each probe is tried **uniformly** (`k` neutral: the class holds at every
step) and, failing that, **peeled** (`k := Succ x`: the class holds at every
step but the innermost, which is taken ordinarily — `half`'s `match k`).

## Why this is sound, and where it sits in the policy

If `s k ih` evaluates on neutral `k`, `ih` to a value in which the only
neutrals are the probe variables themselves (bare, or under projections /
one application), no case split on them happened, so the same reduction
holds for every instantiation (the substitution lemma for `⇝*`). The probe
is therefore a *representation* fact — it reads what the algebra does to a
run, generically — not a definition-shape case: the third kind of
acceleration in [[kernel-acceleration-policy]] is retired, not extended.
The trusted arithmetic is `crates/kernel/src/value/algebra.rs`: a few
hundred lines with a reference semantics in its tests, which is the shape
the verified-kernel-later plan can discharge in Heather-in-Heather.

Probe variables are `Head::Var` at reserved top levels and are checked for
before any probe value is kept; a probe result is never observable. A probe
charges the ordinary fuel (its unfoldings are ones the fold performs anyway
at its first step); a probe that runs out of fuel is `OutOfFuel`, honestly.
Classes are memoized per step closure in the arena.

## Acceptance

- `nat_step_successors` and `nat_step_synchronizes` are gone; every rail
  that pinned them passes on the classes.
- `mul(2^32, 2^32) = pow(2, 64)`, `sub(pow(2,64), pow(2,63)) = pow(2,63)`,
  `leb(pow(2,64), pow(2,63)) = False`, `half(pow(2,64)) = pow(2,63)` are
  `refl` in seconds at the library level, and the same through a
  respelled subtraction the old recognizer did not match. (`toInt` at
  width 64 on a negative value stays absent from `lib_std_bitvec`: it
  folds `Int`'s `ipred`, owned by [[int-arithmetic-over-nat-primitives]].)
- `algebra.rs` tests: composition and iteration against a reference
  interpreter on small counts, the `2^64` DAG cases, overflow composing
  rather than failing, and the peeled/uniform split.
- Probe tests: each class on its canonical algebra, and negatives (a step
  that returns `Succ k`, one that matches on `ih`, one stuck on a glued
  definition under an opaque `Defs`) classify `Opaque`.
- `scripts/bench --check` accepts; the x86 suite's time is unchanged.

## What it assumes from elsewhere

- **[[succinct-inductive-values]]** owns the representation. Assumed: a run
  denotes `Succ^c`, programs compose and cancel as documented.
- **[[kernel-acceleration-policy]]** owns the classification of
  accelerations. Assumed: a representation-generic mechanism with a written
  adequacy argument is the endorsed kind.
- **[[kernel-native-depth-budget]]** owns honest refusal of what is not
  accelerated.

## Out of scope, with owners

- `Int` arithmetic still folds an `Int`-valued `ih` (`isucc`/`ipred`), which
  no Nat class covers; the library answer is `int::add`/`sub` by comparison
  and `nat::sub`, or a sum-typed window class. Filed as
  [[int-arithmetic-over-nat-primitives]].
- `div`/`mod` iterate a two-field state with a decision inside: a state
  machine, not an affine algebra. Not attempted here.

## Log

- 2026-09-09: The `toInt` width-64 negative rail the acceptance list deferred now passes: [[int-arithmetic-over-nat-primitives]] redefined `int::add` over `nat::add` and a synchronous `subNatNat`, both classes this issue built, with no kernel change.
- 2026-09-11: Triage 2026-09-11: landed on 2026-09-09 (eval/probe.rs, value/algebra.rs; DESIGN.md records the third acceleration kind retired; nat_step_successors/nat_step_synchronizes gone from the kernel). Closing; the remaining acceptance rows (2^64 refl timings, bench --check) are covered by the bench and the lib_std_bitvec tests.
- 2026-11-15: The probe this issue added uses fixed reserved levels, which a nested probe reads as its own: [[fold-probe-nested-probe-variable-collision]] (proves False).
