---
title: Conversion never short-circuits on pointer-equal subterms
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

`conv.rs` and `reduce.rs` contain no `Rc::ptr_eq` anywhere (checked
2026-07-31): two literally-shared subterms are re-normalized and compared
structurally like strangers. Pointer-equal terms are syntactically
identical, hence convertible by reflexivity; a `ptr_eq` check at the
`Conv::ty`/`Conv::tm` entry points — *before* whnf — would skip
normalizing both sides.

This compounds with the sharing rounds: [[subst-rebuilds-unchanged-subterms]]
and [[subst-visits-closed-subtrees]] mean conversion increasingly receives
the same `Rc` on both sides (unchanged annotations of two reduction
results of one term, schema pieces instantiated from one skeleton), and
every future round that increases sharing (notably schema caching,
[[schema-construction-caching]]) raises the hit rate further.

## Why it needs deciding, not just doing

- DESIGN.md commits conversion to "ch. 06 verbatim"; a reflexivity
  short-circuit is an extra rule, sound but a deliberate divergence to
  record there.
- Soundness argument to write down: `ptr_eq ⇒` identical syntax `⇒`
  equal in the level-equivalence quotient and equal-as-code, so neither
  the □-syntactic-equality invariant nor the Id-at-□ coincidence
  (DESIGN.md §Algorithms) is disturbed.
- Fuel: a hit spends O(1) instead of the structural cost — that is a
  fuel-*policy* visible change; decide whether a hit still pays `spend()`.
- Pin with a bench (a family whose two sides share, e.g. conv of a term
  against itself post-reduction) so the fast path cannot silently rot.

**Not in scope here:** whnf-result memoization. It is the riskier cousin
(env-dependence, fuel accounting per cached entry) and most of its win on
shared inputs is captured by this check; if a profile ever demands it, it
gets its own issue.

## What it assumes from elsewhere

- **[[subst-visits-closed-subtrees]]** (closed) owns the sharing-preserving
  skip machinery. Assumed here: only that substitution outputs share
  unchanged subtrees, which is what makes hits common.
