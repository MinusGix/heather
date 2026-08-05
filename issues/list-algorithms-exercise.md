---
title: Prove basic list algorithms: the file that ranks the sugar
status: open
labels: [frontend,stdlib,testing,ergonomics]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round). Write a `lib/std`-adjacent
file of small algorithms with real proof content — reverse involution,
append associativity, `nth`-after-`append`, insertion sort sortedness (and
permutation if it fits the budget) — written FIRST in today's language,
then revised as the round's sugar lands.

The point is the method that found [[prelude-option-and-friends]]: the
first real library file exposed the propagation noise no design session
predicted. This file is the falsifier and ranking function for
[[call-site-overapplication]], [[auto-refl-empty-block]],
[[type-owned-members-receiver-slice]], and for whatever it hurts to write
that none of them fix (candidates it may promote: `apply` from
[[surface-proof-automation]], Option chaining from
[[prelude-option-and-friends]], expected-type resolution from
[[type-owned-namespaces]]). Record the before/after of each proof as the
evidence.

Also doubles as a regression/scaling datum: check the file's
`heather check` time against the [[ih-generalization]] cost log's warning
about explicit-motive term size (all runs ulimit-wrapped per CLAUDE.md).

## What it assumes from elsewhere
- **[[ih-generalization]]** owns the varying-argument recursion tax.
  Assumed here: only that insertion sort's inner recursion may hit it and
  the workaround (curried return) is acceptable in this file.
