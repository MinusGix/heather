---
title: Compile a function defined by well-founded recursion on a measure to a loop
status: open
labels: [native,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-25
updated: 2026-10-25
---

[[function-ir-verified-loop-planning]] compiles recursion on an explicit
fuel, `h(fuel, x…)` called as `h(w.toNat(), …)`: the loop's passes are the
fuel, and the program agrees with the source exactly, exhausted bit and
all. A function written by well-founded recursion on a measure of its words
(`Wf`) has no fuel; its loop needs a bound computed from the measure at
entry, and its agreement needs the theorem that the loop never runs out
(`function_ir::loop_runs_unexhausted`: bound the measure plus one, or the
measure where it is positive at every pass).

Two routes:

- Reflect the `Wf` recursion's step the way a fuel's `Succ` arm is
  reflected, and state the agreement by `Wf` induction on the measure
  instead of `Nat` induction on the fuel, the exhausted branch discharged
  by `loop_runs_unexhausted`'s argument.
- Or have the source supply the bound (a fuelled helper, as today) and
  prove once in the library that a fuelled helper with enough fuel is the
  `Wf` function: the compiler then needs no new reflection.

The second is less compiler and more library; it also gives the user's own
fuelled helpers a theorem. Elaboration cost of `Wf` unfolding at open
arguments is the unknown either way.
