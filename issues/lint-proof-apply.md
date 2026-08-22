---
title: "Lint deeply nested proof returns that have a clearer apply script"
status: open
labels: [tooling,lint,frontend,proofs,automation,ergonomics]
blocked-by: [lint-review-only-mode]
created: 2026-08-22
updated: 2026-08-22
---

Once Heather has `apply`, some proof returns written inside-out as nested
function applications will read more clearly as a top-down proof script:

```heather
outer(middle(inner(h)))
```

```heather
apply outer;
apply middle;
inner(h)
```

Add an initially proof-focused lint for sufficiently complex application
spines whose exact `apply` layout is known. This is not a general point-free or
call-style rule: short expressions are often clearer as terms, constructors
often remain clearer as term syntax, and multi-argument applications should be
suggested only when their non-final goal boundaries are unambiguous.

The syntax and semantics owned by [[surface-proof-automation]] are now landed.
The remaining blocker is the review-only rollout mode: this is readability
advice rather than a correctness warning.

## Acceptance

- The first slice is restricted to theorem/proof checking positions. Unary
  continuation chains are the minimum customer; multi-argument suggestions
  use the accepted `give` layout rather than inventing holes.
- Constructors, short one-step calls, named arguments, meaningful partial
  applications, and calls whose continuation is not the selected premise are
  negative controls.
- A complexity threshold is based on structure rather than rendered line
  width, and a stdlib census chooses it.
- The suggested script is parsed and checked to the same elaborated term with
  no new goals or fallback resolution.
- Because this is readability advice, initial rollout uses
  [[lint-review-only-mode]].

## What it assumes from elsewhere

- [[surface-proof-automation]] owns `apply` and its premise/continuation
  semantics.
- [[lint-roadmap]] owns lint infrastructure and rollout policy.

## Log

- 2026-08-22: Filed as a downstream lint owner so `apply` gains a deliberate
  proof-style customer without expanding the feature issue into lint policy.
- 2026-08-22: Updated after `apply` was generalized from a unary proof wrapper
  to ordinary n-ary application in goal order. The lint may eventually suggest
  multi-argument layouts, but it does not trigger meta promotion merely to
  make a rewrite fit.
- 2026-08-22: Unblocked on `apply`: automatic promotion and structured source
  provenance landed with [[surface-proof-automation]]. Review-only lint mode
  is now the sole blocker.
