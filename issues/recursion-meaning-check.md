---
title: Check each structural recursion's unfolding equation, so a miscompile is a refusal
status: open
labels: [recursion,elaboration,soundness-of-meaning]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Structural recursion is compiled at a surface `match`, and when the planner
(`recursion::plan`) misses a form, the result is a well-typed term that means
a different function. The kernel accepts it and `refl` proves the wrong
equation: [[recursion-let-reads-changing-parameter]] (`u(1, x) = x + 1` where
the source says `x + 11`), [[recursive-arm-reads-outer-scrutinee]], and the
branch-on-varied-parameter bug of PR #389 (`v2(1, [3, 0, 4])` compiled to 7,
the source says 0). This is the only class of elaborator bug the kernel
cannot catch (docs/elaborator-principles-survey.md §6).

## Proposal (P4 of the survey)

For every structurally recursive definition, generate its unfolding equation
per constructor of the decreasing parameter,
`f(C(ȳ), x̄) = body[f][n := C(ȳ)]`, and have the kernel check it by
conversion at declaration. A correct compilation should convert (both sides
reach the same arm, with self-calls as `F(k, …)`); each of the three bugs
above differs at an open argument and is refused, located at the definition.
The `decreases` lowering already generates `f_unfold` with a proof
(docs/decreases-unfolding-design.md); structural recursion needs only
conversion.

## Plan

1. A reporting mode over the whole library (a `heather check` flag or a gate
   option) that lists definitions whose equation does not convert. Read the
   list: each entry is either a miscompile (file it) or a false refusal
   (convoy, course-of-values window, dependent ih) to fix or exempt.
2. Turn it into a refusal once the list is empty or every entry has an
   issue. Optionally keep the equations as citable `f_unfold_<Ctor>`
   theorems, as interface definitions already do.

## Acceptance

- The probes from [[recursion-let-reads-changing-parameter]] and #389's
  `v2`, with the planner's refusal disabled, are refused by the meaning
  check, not accepted.
- The library passes in refusal mode.
- Costs stated as a shape: one conversion per constructor per recursive
  definition.
