---
title: Explore composable proof-carrying function analysis interfaces
status: open
labels: [metaprogramming,elaboration,design]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-09-07
updated: 2026-09-07
---

Explore a LifetimeFn-style trait that records analysis requirements and guarantees
with evidence tied to the generated ordinary function. A lifetime declaration
generator may lower limited custom syntax to lifetime parameters, capabilities,
and proof arguments, then export this interface for other analyses to consume.
This is a design issue, not a commitment to a complete Rust-like language.

## Acceptance

- Work through a small concrete memory example before fixing trait parameters.
- Specify requirements and guarantees sufficient for callers, including output
  lifetime relationships and relevant mutation/aliasing/initialization conditions.
- Let automation discharge obligations and users supply checked evidence when
  automation cannot; rejection by an analysis must not define logical invalidity.
- Show how handwritten ordinary functions can participate with the same instance,
  and how calls across analysis worlds preserve the explicit contract.
- Prevent tags or unchecked metadata from standing in for proof of function
  behavior. Keep evidence attached to the exact function and its semantics.
- Separate correctness of generated functions from correctness of the surface
  translation, which additionally needs a semantics for that surface.

## What it assumes from elsewhere

- [[scoped-declaration-generators]] owns syntax lowering and checked expansion.
- [[byte-memory-access-model]] owns memory access semantics, not lifetime analysis.
- [[runtime-compile-opt-in]] owns subsequent compilation eligibility.
