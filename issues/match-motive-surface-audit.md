---
title: "Audit explicit match motives and reconsider the as λ surface"
status: open
labels: [frontend,syntax,elaboration,stdlib,ergonomics]
area: language
created: 2026-08-20
updated: 2026-10-31
---

The standard library currently contains 99 written motives of the form
`match e as λ y => P(y)`. Some express genuinely dependent elimination, but a
written motive is not automatically proof that the author should have had to
write it: motive synthesis is bounded by checking position, scrutinee shape,
and the elaborator's ability to abstract the expected goal.

First audit the sites and classify them as:

1. inferable today and removable;
2. conceptually inferable but blocked by a known elaboration limitation;
3. intrinsically useful because the surrounding expression supplies no result
   type or because the family itself is explanatory.

Then reconsider the irreducible written surface. Candidates include:

```heather
match e as y : P(y) { ... }
match e : λ y => P(y) { ... }
```

The first avoids spelling a lambda while retaining a binder; the second is
shortest but risks reading like a type annotation on `e`. No syntax direction
is chosen before the audit shrinks the customer set. `return` spellings were
considered and rejected: Heather may gain imperative function-body syntax, and
spending that word on an eliminator annotation would make its reading depend
on which part of the language one is in.

## Acceptance

- Every explicit stdlib motive is classified, with counts and representative
  examples.
- Motives made redundant by current inference are removed.
- Each limitation bucket has a bounded owner or a focused elaborator fix.
- The remaining syntax has an unambiguous reading alongside ordinary `as`
  patterns and `:` type annotations, and old syntax receives a migration path
  if it changes.

## What it assumes from elsewhere

- [[motives-as-lambdas]] records why the former bespoke arrow syntax was
  replaced by an ordinary lambda; this issue may reconsider presentation, not
  reintroduce that ambiguity.
- [[convoyed-window-vs-written-motive]] owns one particularly subtle dependent
  interaction and should be one audit category, not duplicated here.

## Log

- 2026-08-20: Filed from the post-cleanup review. The 99-site count is a search
  baseline, not a claim that all 99 motives are required.
- 2026-08-22: `std/nat`'s `le_succ_r` supplied the first audit datum. Moving
  the hypothesis binder from `λ m h => (match m as … { … })(h)` to
  `λ m => match m { … }` puts the inner split in checking position, where the
  existing goal-derived synthesis recovers its dependent function motive; the
  outer motive then synthesizes too. Two motives removed, taking the stdlib
  baseline 99 → 97 with no elaborator change. Discussion also added
  `match e return y : P(y)` to the surface candidates: `return` names the
  semantic role, while `y : P(y)` gives the binder/ascription reading without
  presenting the motive as an ordinary lambda attached to `match`.
- 2026-08-22: The `return` candidate is withdrawn after review: it is too close
  to imperative return, a meaning Heather may need in programming-oriented
  function bodies. The recurring applied-function shape now has the focused
  lint owner [[lint-match-function-application]].
- 2026-10-31: [[match-motive-sweep]] owns the next census (docs/dependent-match-compiler-design.md §1.2: 180 of 379 sampled written motives redundant under --review).
