---
title: Inference does not beta-reduce an Exists proof's type P(witness)
status: open
labels: [elaboration,inference]
created: 2026-10-16
updated: 2026-10-16
---

Projecting the proof out of an `∃` that a call returns gives a value whose
type is `P(witness)` with `P` still a λ. Implicit-argument inference does
not β-reduce it before matching:

```heather
theorem t(d: Rat, close: (k: Nat) → d <= Rat::inv_succ(k), positive: Rat::zero() < d): False {
    let gap = d.archimedean_inv(positive);
    Rat::not_le_of_lt(gap.proof, close(gap.witness))
    // error: could not infer the implicit argument `x` of `Rat::not_le_of_lt`
}
```

Matching on `Exists(k, gap)` instead fails the same way. What works is
restating the type, `let below: (Rat::inv_succ(k) < d) = gap;`, which the
regular Cauchy reals do at every such site (`Rat::same_of_close`,
`CReal::ofRat_lt`).

Wanted: when inference unifies an implicit's occurrence against a type
whose head is a β-redex (an applied λ, or a record field type instantiated
at a projection), it reduces the redex first. The type here is closed and
the reduction is one β step, so no higher-order unification is involved.

Acceptance: the snippet above checks, both for the `.proof` projection and
for the `match` binder. A negative control with a wrong `close` is still
refused.

## What it assumes from elsewhere

- **[[exists-type-arg-not-inferred]]** (closed) fixed inference of
  `Exists`'s type argument at introduction. This is elimination.
