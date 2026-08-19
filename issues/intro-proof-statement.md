---
title: "intro as a checking-position proof statement"
status: open
labels: [frontend,syntax,proofs,ergonomics]
created: 2026-08-19
updated: 2026-08-19
---

Short proof lambdas are readable today, but they force the writer to repeat a
domain that the goal already supplies and become visually heavy inside match
arms. The representative Int proof is:

```heather
theorem not_lt_of_ge(a, b: Int, h: a <= b): ¬ (b < a) {
    λ (back: b < a) => lt_irrefl(a)(lt_of_le_of_lt(a, b, a, h, back))
}
```

A checking-position statement should permit:

```heather
theorem not_lt_of_ge(a, b: Int, h: a <= b): ¬ (b < a) {
    intro back;
    lt_irrefl(a, lt_of_le_of_lt(a, b, a, h, back))
}
```

`intro x; rest` is the statement-position face of `λ x => rest`: it requires
the expected goal to reduce to a Pi, binds the domain under the requested name,
and checks the continuation at the codomain. `intro x y;` should peel a Pi
spine in order. An optional annotation may be allowed as a checked ascription,
but inference from the goal is the feature.

This is deliberately smaller than a second tactic language. Heather already
has the other two common proof shapes:

- the trailing block expression is `exact`, so an `exact` keyword adds no
  capability;
- `split e; on Ctor(...) := ...;` is structurally named `cases`, and
  `on _ := body` applies one shared body to every remaining constructor.

The motivating repeated-lambda arms then read:

```heather
match m as λ z => n < z -> NegSucc(z) < NegSucc(n) {
    Zero => { intro bad; false_elim(bad) },
    Succ(k) => { intro good; good },
}
```

An all-goals combinator analogous to Lean's `<;>` is not part of the first
slice. The current `split m; on _ := trivial;` already covers the motivating
uniform-constructor case; add a goal-map combinator only when a second command
sequence genuinely wants it.

## Acceptance

- One and several introductions work in theorem bodies and nested block
  expressions, including match arms.
- Dependent codomains see the introduced binder correctly.
- A non-Pi goal refuses at `intro` with the actual goal type.
- The emitted term is definitionally equal to the explicit lambda spelling.
- `split`/`on`, holes, and later `apply` statements compose without inventing a
  separate tactic state.

## What it assumes from elsewhere

- **[[surface-proof-automation]]** owns `apply` and the future solver slot.
  `intro` should share its continuation/block machinery, not its automation.
- **[[split-on-arms]]** owns the existing `cases`-shaped construct.

## Log

- 2026-08-19: Filed from the post-I-prime proof-style review. The decision to
  omit `exact` and defer an all-goals combinator is intentional: the ordinary
  trailing expression and `split` default arm already cover those two examples.
