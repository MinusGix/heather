---
title: "Investigate first-class function composition notation"
status: open
labels: [frontend,syntax,operators,functions,programming,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

Investigate first-class function composition, provisionally `f ∘ g`, whose
result is a function equivalent to `x ⊢ f(g(x))` rather than an application
performed immediately.

Composition is distinct from both [[pipeline-operator]] and
[[surface-proof-automation]]: it must preserve a callable for later use, cope
with implicit and dependent function types, and say when eta-expansion is
required because a constructor or other checking-only head is not itself an
inferable function value.

## Acceptance

- Operand/result types, order, precedence, associativity, and universe behavior
  are specified.
- Polymorphic functions, implicit binders, dependent codomains, constructors,
  and computed function values have explicit examples or refusals.
- The design decides whether composition is a built-in elaboration form, a
  designated library operation, or parser sugar for a lambda.
- The notation does not claim equivalence where eta or expected-type
  information makes the direct expansion elaborate differently.

## What it assumes from elsewhere

- [[pipeline-operator]] owns immediate value-first chaining.
- [[surface-proof-automation]] owns immediate goal-first application.
- [[notation-extensibility]] owns the general operator namespace.

## Log

- 2026-08-22: Filed as an independent function-producing construct rather
  than a compact spelling of an `apply` chain.
