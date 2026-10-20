---
title: "Lint local bindings whose names are never used"
status: open
labels: [tooling,lint,frontend,blocks,ergonomics]
area: language
created: 2026-08-22
updated: 2026-08-22
---

A successfully elaborated local binding whose name contributes to no later
statement, result, type, or goal discharge is dead structure:

```heather
let witness = expensive_proof(x);
result
```

Warn on the binding and offer deletion of the complete statement. Heather is
pure and total, so evaluating an unused value has no effect to preserve, but
the lint is still more useful than a textual name scan: dependent later types,
shadowing, quotation/splicing, and `on` targets all make binding identity
matter.

The initial rule is for `let` statements only. Parameters and global
declarations have different intent: an unused theorem hypothesis can document
a stronger interface, and an apparently unused global can be public API.

## Acceptance

- A local `let` binder unused by every later statement, the block result, and
  every applicable `on` discharge is reported.
- Uses in value expressions, type annotations, motives, quotations/splices,
  and goal targets all count.
- Shadowing is resolved by binding identity rather than spelling.
- `_` and elaborator-generated binders are silent.
- The structured fix removes the whole statement, including its terminating
  semicolon, and the edited declaration is verified to elaborate.
- Failed and generated declarations produce no finding.

## What it assumes from elsewhere

- [[lint-roadmap]] owns rollout policy. This is intended for the conservative
  default after a stdlib census.

## Log

- 2026-08-22: Filed from the post-stdlib-warning review. Scope deliberately
  excludes unused parameters and globals; local dead structure is the
  high-confidence customer.
