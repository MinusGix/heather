---
title: "Lint proof lambdas that read better as sequent binders"
status: open
labels: [tooling,lint,syntax,proofs,stdlib,ergonomics]
area: language
created: 2026-08-22
updated: 2026-08-22
---

The checking-position sequent binder is Heather's proof-introduction spelling,
but older proof branches still wrap their result in ordinary lambdas:

```heather
match n {
    Zero => λ bad => false_elim(bad),
    Succ(_) => λ good => good,
}
```

In proof-oriented checking positions, prefer:

```heather
match n {
    Zero => bad ⊢ false_elim(bad),
    Succ(_) => good ⊢ good,
}
```

Both spellings lower to the same `ExprKind::Lam`, so this is a written-source
lint. It must inspect the lambda token/span rather than warning on every lambda
AST. The initial high-signal slice is an explicitly written lambda used as a
match-arm body inside a theorem, where `⊢` removes punctuation and reads as
introduction under an assumption. Value-returning functions and lambdas used
as first-class values remain ordinary lambdas.

## Acceptance

- The first slice recognizes explicit lambda match-arm bodies in theorem-owned
  proof expressions when the arm is checked at a function-shaped goal.
- It does not report sequent binders, generated lambdas, value-producing
  function definitions, inferred function values, motives, or quotations.
- Multiple binders and checked binder annotations produce an exact `x y ⊢`
  or `(x: A) ⊢` replacement.
- The suggested spelling is reparsed and checked to the same elaborated term.
- A stdlib census decides whether theorem bodies outside match arms are clear
  enough for the same rule or belong only in review mode.

## What it assumes from elsewhere

- [[sequent-binder-expression]] owns the syntax and its equivalence to lambda.
- [[lint-roadmap]] owns profile and rollout policy.

## Log

- 2026-08-22: Filed from the std warning cleanup, where checking-position
  rewrites left several proof branches expressed with function-construction
  punctuation instead of Heather's introduction form.
