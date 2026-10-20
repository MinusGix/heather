---
title: The calculator showcase's repeated shapes name two gaps in the parser client API
status: open
labels: [frontend,parsing,stdlib,proofs,ergonomics]
area: heather-in-heather
created: 2026-09-16
updated: 2026-09-16
---

`docs/showcase/calc_parser.hthr` is the checked parser library's most complete
client, so the boilerplate it writes is evidence about the library's API. Two
shapes repeat there, and neither is about the calculator.

**1. Four copies of one inversion proof.** `plus_selected`, `times_selected`,
`opening_selected` and `closing_selected` are the same theorem with one
constructor moved:

```heather
theorem plus_selected(token: PTok, value: Nat): plus(token) = Some(value) -> token = TPlusSym {
    match token { TPlusSym => λ h => refl, TNum(_) => λ h => absurd(h), TStarSym => λ h => absurd(h),
        TOpen => λ h => absurd(h), TClose => λ h => absurd(h) }
}
```

The content is "this partial selector returns `Some` on exactly one
constructor, and here is the inversion". `symbol_span` already abstracts the
*use* of these proofs over `pick`/`token`/`selects`, so the library knows the
shape — what it does not offer is a way to *produce* the witness. Options
worth costing against each other: a derivation for selectors defined by a
single-constructor match; a `parser` helper that takes the selector and the
constructor and returns the inversion; or leaving it, if the honest answer is
that four lines of `absurd` per token class is the right price.

**2. A dummy parameter.** `TokenSpan(token, source, begin, end, ignored: Nat)`
carries `ignored` to match an arity nothing reads. A parameter named `ignored`
usually means the abstraction it belongs to is one step away from the one that
was wanted — either `TokenSpan` should not be parameterized this way, or the
thing it lines up with should not be.

Neither is urgent. Both are the kind of thing that is invisible from inside the
library and obvious from its only large client, which is why they are recorded
now rather than rediscovered.

## What it assumes from elsewhere

- **[[parser-certified-composition-cost]]** owns the checked parser library's
  cost. Assumed here: nothing about cost — these are API-shape observations,
  and a derivation that replaced the four proofs would have to be measured
  there before it counted as an improvement.

## Log

- 2026-09-16: Filed from the `calc_parser.hthr` readability pass, alongside
  [[result-eliminator-explicit-type-arguments]].
