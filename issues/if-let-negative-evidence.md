---
title: Give an if-let failure branch evidence that the pattern did not match
status: open
labels: [frontend,elaboration,patterns,proofs,design]
area: language
created: 2026-08-19
updated: 2026-08-19
---

After [[let-else-sugar]] lands its V1 one-pattern match, allow the `else`
branch to name evidence that the pattern cannot match the scrutinee. This is
wanted, but deliberately not part of V1.

For `Some(x)` the proposition is not merely `y != Some(x)`, because `x` is
bound only in the successful branch. The branch-independent statement is
closer to:

```text
¬ Exists(λ x => y = Some(x))
```

In general the frontend needs a `Matches(pattern, scrutinee)` proposition that
existentially packages pattern binders and constructor equations; the failure
evidence has type `¬ Matches(...)`. Nested patterns compose those packages.
Wildcards and repeated/refined fields need an explicit account rather than an
accidental encoding.

The evidence is computationally available from the same constructor split;
it should not require resolving an unrelated `Decide` instance. The hard part
is constructing a useful, printable proposition and its refutation across all
remaining arms, especially for indexed families where homogeneous constructor
equations may not exist.

Syntax is intentionally unsettled. It should follow the evidence-binding
style of decidable `if` and [[let-else-sugar]], but must not overload the one
name in a way that gives it unrelated types without clear branch scopes.

## Acceptance

- A simple `Option` failure branch receives evidence definitionally equivalent
  to `¬ ∃ x, y = Some(x)` and can use it in a proof.
- Success binders do not escape into the negative proposition.
- Nested patterns have a stated `Matches` composition and a computation test.
- Indexed-family and wildcard boundaries are decided explicitly.
- Omitting the negative binder emits exactly the V1 match term, so ordinary
  `if let` pays no proof-construction tax.

## What it assumes from elsewhere

- **[[let-else-sugar]]** owns ordinary `if let`, its success equation, and the
  one-row match lowering. This issue begins only after that scope lands.

## Log

- 2026-08-19: Split from the `if let` design discussion. Negative evidence is
  a desired feature, but its existential `Matches` proposition is materially
  larger than the V1 one-row match and therefore has its own owner.
- 2026-08-19: UNBLOCKED when positional `if let` V1 landed.
- 2026-11-14: A narrower, positive form is built (`docs/language/when-design.md` §11,
  "The `else` that knows why", Minus: every type, every field): a `_` arm
  standing for exactly one constructor binds that constructor's fields under
  `__else_N_j`. For a two-constructor type that is the negative evidence's
  content without a `Matches` proposition. This issue's general form (several
  remaining constructors, the equation to the scrutinee, a nameable binder)
  stays open.

