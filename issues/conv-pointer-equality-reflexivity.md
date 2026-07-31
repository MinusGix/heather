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

## Log

- 2026-07-31: Denominator note after the Psi-clone and level-fast-path rounds (release heather check lib/ir_v1.hthr: 2.1s -> 1.305s). Conversion is now the top block in its own right -- Conv::ty 6.6% self, whnf_ty 3.6%, whnf_ty_opaque 2.9%, plus Rc<Term>::drop_slow at 6.9% and Type drop glue 3.8% just behind, which is the shape of a walk that re-descends structure it could have recognized. Nothing here was measured directly and the trigger is unchanged; recorded only so the percentages in this file are not read against the old 2.1s run. Adjacent evidence in favour: the same reflexivity shortcut taken for levels this round ([[level-normalization-allocation]]) was worth 11% of the whole run on its own.
- 2026-07-31: Scoping datapoint from the deep-path investigation ([[whnf-sharing-term-growth]]): reflexivity short-circuits cannot help the add(2,3)-through-LetCall path. Its whole cost (~56% substitution + allocate/free/drop, the rest bounds probes) is PRODUCING the normal form; by the time two terms are compared the work is already spent, and the sides are never pointer-equal. Noted so this issue is not reached for as a deep-path lever.
