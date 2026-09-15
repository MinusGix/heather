---
title: Propagate expected map results into checking-only callback bodies
status: closed
labels: [frontend,elaboration,inference,ergonomics]
created: 2026-09-14
updated: 2026-09-14
---

## Reproduction

At `e4b3836`, in `docs/showcase/calc_parser.hthr`, a theorem equates the compiled result
with a map over `calculate(ts)`. With `result::map` explicitly qualified,
`λ (n: Nat) => Some([n])` failed because the collection literal had no
expected container type. Supplying
`result::map<Nat, Option<List<Nat>>, ParseError>(...)` checks. The enclosing
equality constrains the mapped result to `Result<Option<List<Nat>>, ParseError>`.

Minimize this precise checking-context path. Existing per-call postponement
already exists: determine where usable expected-type information is lost or
arrives too late before expanding inference machinery.

## Acceptance

- The qualified map in the calculator theorem checks without spelling its
  recoverable type arguments; the callback's `[n]` is checked as `List<Nat>`.
- Exercise an explicitly expected result, an equality endpoint, neutral
  inputs, open payload types, and nested checking-only constructors.
- Defer a callback when other available constraints can determine its
  domain/codomain; retain ordinary annotation requests when genuinely
  underconstrained. Do not default an unconstrained collection to List.
- Reject a wrong element/container type and a false theorem; preserve
  dependent argument scoping, occurs checks, and existing inference cases.
- Establish whether the fix is within the existing per-call mechanism; a
  broader cross-call change needs its own evidence and design justification.

## What it assumes from elsewhere

- **[[elab-unifier-completeness]]** owns general postponement boundaries;
  assumed here: existing per-call solving is available for the repro.
- **[[named-argument-checking-context-loss]]** owns checking-context loss in
  named arguments; this callback/equality client is independently scoped.
- **[[result-map-receiver-dispatch]]** owns method selection; qualification
  isolates this issue from that failure.
- **[[parser-combinator-library]]** is the downstream library customer.

## Log

- 2026-09-14: [[result-map-receiver-dispatch]] changes the checked calculator
  spelling to `.map(λ (n: Nat) => Some<List<Nat>>([n]))`. This issue now removes
  that recoverable callback/container annotation. Keep the explicitly
  qualified-map repro as an independent test of expected-type propagation.
- 2026-09-14: Implemented within existing per-call postponement. Fully
  annotated lambdas prefer checking when their parameter type is unsolved,
  retaining inference fallback when the callback must teach its result type.
  The global checking-only classifier and cross-call inference are unchanged.
  Both calculator pipeline laws now use `.map(λ (n: Nat) => Some([n]))`.
  Design: `docs/callback-expected-types-design.md`. Five regression tests
  cover expected results, later arguments, neutral/open inputs, dependent
  scoping, inference fallback, and rejection controls. Full `scripts/test`:
  **2652 passed, 0 failed, 5 ignored**. Reversed equalities whose left endpoint
  cannot infer need a separate endpoint-selection change, owned by
  [[equality-endpoint-checking-context]]; this checking-context scope is done.
- 2026-09-14: The isolated benchmark gate reports seven Nat timing flags,
  with no slope failures; recorded under [[kernel-benchmark-nat-baseline-drift]].
  No kernel or benchmark changes and no baseline rewrite.
