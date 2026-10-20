---
title: "Lint removable explicit type arguments and implicit-insertion escapes"
status: open
labels: [tooling,lint,frontend,elaboration,inference,ergonomics]
area: language
created: 2026-08-22
updated: 2026-08-22
---

Explicit type arguments and `@` are essential escape hatches when inference or
implicit insertion cannot choose the intended application. They also tend to
remain after inference improves, leaving source that advertises a constraint
which no longer exists.

For a qualifying application, speculatively elaborate the less explicit
spelling and warn only when it resolves to the same declaration, inserts the
same implicit arguments, and produces a definitionally equal term/type without
new goals or fallback routes. Prefer removing the smallest independently
redundant annotation rather than proposing an all-at-once rewrite whose success
depends on several removals interacting.

This is likely profile-only initially. Explicit arguments can document a
non-obvious carrier even when inference succeeds, and `@` can intentionally pin
the visible calling convention. Without per-site suppression, only especially
obvious cases should enter the conservative default.

## Acceptance

- Type applications and `@` have separate findings and explanations.
- The suggested source is speculatively checked with transactional elaborator
  state and resolves to the same semantic application.
- Ambiguity, overload/designation choice, named arguments, partial application,
  recursive self-calls, and inference that succeeds only through a fallback
  are negative controls.
- Removing one annotation at a time yields stable, non-cascading diagnostics.
- A library census decides default versus stdlib-profile rollout.

## What it assumes from elsewhere

- [[lint-roadmap]] owns profile policy and sequencing.
- [[implicit-binders-in-function-types]] owns `@` semantics; this issue only
  identifies an invocation where using that escape changes nothing.

## Log

- 2026-08-22: Filed from the lint review with speculative equivalence as the
  required evidence; syntactic guesses are explicitly out of scope.
