---
title: Plan recursion on binder identities, and compile the recursion at the top
status: closed
labels: [recursion,elaboration,design]
area: language
created: 2026-11-02
updated: 2026-11-04
---

The recursion planner (`recursion::plan`, `reads`, `bind_statement`) decides
the lowering on the **surface**, with a name-keyed scope (`Bound { name:
String, … }`, `lookup` by string), and every form it does not list falls
through `surface::for_each_child` without binding. By reading (not yet
probed): `Stmt::LetCode` binds a name `bind_statement` does not record, and
`ExprKind::MatchCode`'s arm binders are not bound, so a shadowing binder in
either is read as the outer name. Every new binding form has to be added
here as well as in the elaborator. Measure lifting has the same shape
([[decreases-shadowed-let]]; the `while` lowering works around it with
`alpha.rs`'s SSA renaming). Together with the guard-selection rules
([[recursion-guard-takes-nearest-parameter-match]],
[[recursion-outer-match-takes-guard-without-descent]],
[[recursion-case-split-dependent-ih]], #389's varied branch), this is a
second scoping semantics that drifts from the elaborator's
(docs/elaborator/elaborator-principles-survey.md §6.2).

## Proposal (P5 and §6.3)

Design round, two steps:

1. **Binder identities.** The planner and measure lifting run after one
   uniform renaming of every binding form (generalise `alpha.rs`), or on the
   elaborated body, where binders are positions and scoping is the
   elaborator's own.
2. **Recursion at the top.** Compile the whole body against a `below`
   structure on the decreasing argument with every other parameter
   generalised in the motive (Lean's `brecOn`), self-calls as projections.
   Then the match's position is irrelevant, the body recomputes at each
   level, and guard selection, stale lets, varied branches, dependent ihs and
   course of values at depth d stop being questions. Heather has `below` for
   `Nat` (docs/language/recursion/course-of-values-recursion-design.md); the general one needs
   one per lowered inductive tier.

[[recursion-meaning-check]] keeps whichever lowering is in place honest
meanwhile, and should land first.

## Acceptance

A design note decided by Minus, stating which of the issues above it
retires, with the first slice filed. Probes for the `LetCode` and
`MatchCode` shadowing readings above, as accepted or refused, either way
with the right meaning.

## Log

- 2026-11-02: Step 1's renamer exists since #393: `alpha::deshadow` (used by the `decreases` lowering via `measure::deshadowed`). The structural planner does not run over it yet.
- 2026-11-03: 2026-11-03: Design note docs/language/recursion/recursion-at-the-top-design.md (options A below-at-the-top staged, B binder identities only, C keep patching; A recommended), awaiting Minus's choice. Probes in lib/_tests/std/core/recursion_binder_tests.hthr: the LetCode and MatchCode readings are unreachable today (a meta fn cannot call itself; code types are refused outside meta fn signatures; nested let code is refused), each an expect-error with its reason; an unused `let j = n` in the recursive arm is refused, which A would accept. Slice 1 filed as [[recursion-below-nat-fallback]]. Side find: [[meta-fn-mismatch-reaches-kernel]].
- 2026-11-04: 2026-11-04: Minus chose option A (below at the top, staged). The design note's acceptance is met: decided, slice 1 filed as [[recursion-below-nat-fallback]], probes in lib/_tests/std/core/recursion_binder_tests.hthr. Closed; the slices carry the work.
