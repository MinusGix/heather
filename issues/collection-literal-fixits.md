---

`manual-list-construction` detects a finite `Cons(…, …Nil)` spine and suggests
`[…]`, but the warning carries only text. Offer a structured source edit for
the finite spine when it can be rewritten without losing comments or changing
the formatting ownership of nested expressions.

## Acceptance

- The fix rewrites only a semantically resolved canonical List spine.
- Element source text is preserved exactly where practical.
- Comments between constructors, commas, and the final `Nil` are either
  preserved at a defined location or cause the fix to be withheld.
- Parenthesization remains correct for every element expression.
- Recursive/open-tail construction and patterns offer no fix.

## What it assumes from elsewhere

- **[[list-literal-syntax]]** owns literal syntax and lint detection. Assumed
  here: only that the warning identifies one outer finite spine.
- **[[canonical-list-literal-identity]]** owns which List declaration receives
  the lint. Assumed here: only its semantic identity result.

## Log

- 2026-08-30: Filed from the generic collection-literal follow-up review.
title: Offer structured fixes for manual list construction
status: open
labels: [frontend,lint,ergonomics]
created: 2026-08-30
updated: 2026-08-30
---

