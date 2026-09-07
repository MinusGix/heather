---
title: Refuse excessive computation with OutOfFuel before the native stack overflows
status: open
labels: [kernel,evaluator,diagnostics]
created: 2026-09-07
updated: 2026-09-07
---

The evaluator keeps its tail positions on a trampoline (`Eval::drive`), so a
divergent chain of reductions returns `OutOfFuel`. Its *non-tail* positions
— a scrutinee, an application's function, a type annotation — stay on the
native stack, by design, "where its depth is the syntax's". That premise
fails for a computation whose *value* nests scrutinees: `iterate_increment`
builds `increment(n, ih)` with `ih` the pending elimination of the previous
increment, and `increment` matches on it, so forcing the head bit of
`add(64, a, b)` recurses natively once per unit of `toNat(b)`. With a `2^63`
count the process aborts with a stack overflow long before the 2^20 fuel is
spent, at every stack size tried (512 KB–8 MiB, release build) —
`signed_overflow_add(64, s, s)` over two sign-1 sums in
[[bitvec-closed-reduction-cost]]'s consumer rail, and `nat::half(1048576)`
(course-of-values recursion) before it. A SIGABRT is not a verdict, and the
checker is meant to be total on ill-typed input.

## Plan

- A **depth budget** beside the fuel: count native re-entries of
  `Eval::drive` (and conversion's recursion, if it can be reached the same
  way) and return `OutOfFuel` when the count exceeds a bound sized well
  below the thread's stack. Same policy as fuel — a budget that answers must
  agree with the answer the full budget gives, so the bound is an invariant
  on *whether* the machine answers, never a cost model — and the same
  reporting (`out of fuel reducing a term`), possibly with a distinct reason
  text so the diagnosis is not misread as fuel.
- Measure the frame cost per re-entry in debug and release
  (`stack/check-numeral` in `scripts/bench` already bisects depth for the
  checking walk) and size the bound from the 8 MiB `RUST_MIN_STACK` rail in
  `scripts/test`, not from the desktop.
- Alternatives to keep in view: moving scrutinee evaluation onto the
  trampoline (a `Frame` for "elimination waiting for its scrutinee's value")
  removes this class rather than bounding it, at the cost of the machine's
  simplest invariant; a guard page/`stacker`-style growth hides the abort
  but not the cost. Bounding first is the cheap, verdict-neutral step.

## Acceptance

- `theorem t(): nat::half(1048576) = 524288 { refl }` and
  `signed_overflow_add(64, s, s)` over two sign-1 width-64 sums are refused
  with `OutOfFuel` (or the new reason) under `scripts/test`'s rail instead of
  aborting the test binary; both become permanent refusal controls.
- The kernel's fuel-sensitivity tests (`low_fuel_never_produces_a_wrong_answer`
  and the conversion fixtures) still pass; `scripts/bench --check` shows no
  exponent change and `stack/check-numeral` no depth loss.

## What it assumes from elsewhere

- **[[bitvec-closed-reduction-cost]]** owns the resource-diagnostic clause
  this issue implements; [[numeral-stack-depth]] owns the checker's own
  (syntactic) depth.
- **[[bitvec-width-bounded-defaults]]** removes the library's largest source
  of such computations; this issue is about what happens when one remains.
