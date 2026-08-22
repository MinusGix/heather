---
title: "Lint trivial lambdas that have a clear argument-slot spelling"
status: open
labels: [tooling,lint,syntax,stdlib,ergonomics]
created: 2026-08-20
updated: 2026-08-20
---

Heather's argument slot gives basic functions and one-use eta wrappers a much
quicker spelling:

```heather
λ x => x                 // ·
λ p => false_elim(p)     // false_elim (eta-reduce to the function)
λ p => Inr(p)            // Inr(·) (checking-only constructor section)
λ x y => f(x, y)         // f(·, ·)
```

Add a conservative lint for cases where this rewrite is capture-free and the
smallest checking-position ownership is unambiguous. The rule should not erase
a name that documents a nontrivial hypothesis merely because it occurs once.

## Acceptance

- Identity lambdas and direct one-use eta wrappers receive the corresponding
  shortest valid suggestion.
- A direct wrapper around a first-class function prefers eta-reduction to the
  function itself (`false_elim`), while a checking-only constructor wrapper
  may prefer the explicit section (`Inr(·)`).
- Multiple, repeated, reordered, and discarded arguments use indexed slots
  only when the result is strictly clearer and supported by
  [[argument-slot-sections]].
- The lint does not cross a nested lambda/binder, change capture, or suggest a
  slot where ownership would move to a different checking position.
- A named binder can be retained without warning when it carries explanatory
  value; the rollout begins warning-only against the cleaned stdlib baseline.

## What it assumes from elsewhere

- [[stdlib-surface-style-lint]] owns the common lint infrastructure.

## Log

- 2026-08-20: Filed from the cleanup that changed the Int negative-base arm
  from `λ (h: NegSucc(0) < NegSucc(0)) => h` to simply `·`.
- 2026-08-22: Preference refined after review: do not manufacture an argument
  slot when ordinary eta-reduction already yields the named function;
  constructor sections such as `Inr(·)` remain the case where the slot reads
  better and supplies checking-position construction.
