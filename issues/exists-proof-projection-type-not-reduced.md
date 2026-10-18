---
title: Inference does not beta-reduce an Exists proof's type P(witness)
status: closed
labels: [elaboration,inference]
created: 2026-10-16
updated: 2026-10-18
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

## Log

- 2026-10-18: FIXED. The subject type was `El(app@(λk. Rat::Lt(inv_succ(k), d); witness))`,
  and the application congruence in `unify_tm` (crates/elab/src/unification.rs) paired the
  pattern's spine against the λ and its argument: `?x` learned nothing and `?y` learned the
  *witness*, a wrong solution the kernel would have refused had `x` not been reported first.
  Now `unify_tm` contracts a subject's head β-redexes (`beta_head`, context-free `inst_top`)
  before any other rule, and `unify_ty` does the same to an `El` subject's code before
  decoding, so a predicate that is an equation reads as an `Id` against a pattern `a = b`.
  Head-only and syntactic: no δ, no context, nothing a well-typed term reduces forever.
  Test: crates/elab/tests/logic.rs `an_exists_proof_read_off_a_call_teaches_implicits`
  (`.proof` and `match` binder, a named predicate and an equation, a wrong-statement
  negative control). Library: `Rat::same_of_close` and `Rat::le_of_le_add_inv_succ` drop
  their restating `let`s; `CReal::ofRat_lt` keeps its own (creal.hthr had other rounds open).
