---
title: A match silently loses its motive when the goal's stuck head is slow to spell
status: open
labels: [elaborator,diagnostics]
area: language
created: 2026-11-10
updated: 2026-11-10
---

A `match` on a scrutinee that occurs in the goal gets its motive by
abstraction (`synthesize_motive`, `crates/elab/src/matching.rs`). When the
scrutinee is not syntactically there, the goal's stuck head is spelled by
the small-step reducer and abstracted from that
(`abstract_stuck`), under a budget: `STUCK_SPELLING_STEPS = 64`
(`crates/elab/src/oracle.rs`). Past the budget the fallback is the goal
unabstracted, with no note.

So a change that makes a goal's stuck head *more expensive to spell*,
with nothing else different, turns a proof that checked into one that
fails, and the error is at the arms (`trivial` proves `True`, but the
whole unrefined goal is expected), nowhere near the cause. Met when the
register file became data (`File::branch_test` in `emit_calls_emits`,
`function_ir_lower_calls.hthr`): reading a slot is four projections
where it was one application, the spelling passed 64 steps, and one
`Conditional` arm lost its motive, with nine cascading errors after it.
The motive is written out there now.

## Directions

- Say so: when the spelling budget is what stopped the abstraction, the
  mismatch error at the arm carries a note naming the scrutinee and the
  budget, and suggests `as`.
- Or spell with the evaluator (which shares) and read the stuck head back,
  so the budget is not in steps of the slowest reducer.

## Done when

A proof whose motive is lost to the spelling budget is told so at the
`match`, with a test that reproduces it by a goal whose stuck head takes
more than the budget to spell.
