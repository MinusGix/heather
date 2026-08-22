---
title: "Investigate a value-first pipeline operator"
status: open
labels: [frontend,syntax,operators,programming,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

Investigate a conventional value-first pipeline, provisionally `|>`:

```heather
value |> prepare |> finish
```

Unlike [[surface-proof-automation]]'s outer-first application blocks, a
pipeline presents computation in dataflow order. Decide whether it is pure
parser lowering to nested application, how additional/named arguments place
the piped value, how expected-type inference flows through the lowering, and
whether future effects change evaluation-order expectations.

Do not use the pipeline as alternate syntax for multi-goal `apply`; branching
application trees and promoted inference obligations remain owned there.
Producing a reusable composed function instead of immediately passing a value
is separately owned by [[function-composition-operator]].

## Acceptance

- Direction, precedence, associativity, and argument position are explicit.
- Unary calls, calls with existing arguments, methods, constructors, and
  checking-only expressions have positive and negative examples.
- The elaborated term and evaluation order are stated relative to ordinary
  application.
- Interaction with carrier-directed operator designations is decided rather
  than assuming `|>` can be reserved globally.

## What it assumes from elsewhere

- [[surface-proof-automation]] owns goal-oriented, outer-first application.
- [[notation-extensibility]] owns the general operator namespace.

## Log

- 2026-08-22: Filed separately from `apply`: equal unary normal forms do not
  make value-first dataflow and goal-first construction the same source model.
