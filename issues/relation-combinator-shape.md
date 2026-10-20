---
title: Decide whether relation combinators should uniformly return relations
status: open
labels: [stdlib,logic,semantics,ergonomics,design]
area: mathematics
created: 2026-08-26
updated: 2026-08-26
---

`Compose`, `Graph`, `AnyOf`, and `Steps` return relation values, while `RelId`,
`Converse`, `RelChoice`, and the framing combinators take their endpoints in
the same argument list.  Both forms elaborate, but the mixture is visible in
higher-order statements and explicit type arguments.

Try both shapes in composition, framing, and client theorem statements.  Then
either normalize the API or record why the mixed shape gives Heather better
inference or call-site readability.  Compatibility aliases are sufficient if
a migration would otherwise create churn.

## What it assumes from elsewhere

- **[[relational-semantics-refinement-kit]]** owns the current public API.
- **[[polymorphic-argument-with-unsolved-callee]]** owns the inference failure
  that may constrain an apparently cleaner higher-order shape.
