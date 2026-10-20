---
title: "Lint matches whose reachable arms do no meaningful case analysis"
status: open
labels: [tooling,lint,frontend,patterns,proofs,ergonomics]
area: language
blocked-by: [lint-review-only-mode]
created: 2026-08-22
updated: 2026-08-22
---

A match can remain after a proof refactor even though every reachable arm has
the same binder-independent body:

```heather
match decision {
    Yes(_) => done,
    No(_) => done,
}
```

Recognize these vacuous case analyses and suggest the common body when it
checks outside the arms. This is not the existing unreachable-arm lint: every
arm may be reachable while the distinction between them contributes nothing.

The semantic claim needs care. A neutral match with identical arms is not in
general definitionally equal to the common body, even in a pure total
language. The lint must therefore describe a simplification, not claim kernel
convertibility, and its initial rollout belongs in the review-only tier unless
a narrower definitionally verified subset proves useful.

## Acceptance

- Only reachable arms participate; an existing unreachable-arm finding is not
  duplicated.
- The common body is independent of pattern and equation binders, with
  shadowing handled by identity.
- The match is exhaustive and has at least one reachable constructor; empty
  elimination is never called vacuous.
- Replacing the whole match by the common body is speculatively checked at the
  same expected type without new goals, fallback resolutions, or warnings.
- Syntactically different bodies are considered equal only if a deliberately
  specified semantic comparison justifies it; the first slice may require
  identical written bodies.
- Dependent motives and recursive matches have explicit negative controls.

## What it assumes from elsewhere

- [[lint-roadmap]] owns rollout policy.
- [[lint-review-only-mode]] supplies the initial non-default presentation.

## Log

- 2026-08-22: Filed from the clean-stdlib lint review. The issue records the
  intensional caveat rather than silently equating identical branch behavior
  with definitional equality.
