---
title: A let above a recursive match keeps the top call's value of a parameter the self-call changes
status: closed
labels: [elaboration,correctness,recursion]
area: language
created: 2026-11-02
updated: 2026-11-02
---

A structurally recursive `fn` whose recursive call **changes another
parameter** computes a wrong answer when a `let` above the recursive `match`
reads that parameter: the `let` keeps the top call's value at every level.
The kernel accepts the wrong equation by `refl`:

```
fn u(n: Nat, x: Nat) → Nat {
    let y = x + 1;
    match n { Zero => y, Succ(k) => u(k, x + 10) }
}
theorem wrong(x: Nat): u(1, x) = x + 1 { refl }   // checks; the source says x + 11
```

Without the `let` (`Zero => x + 1`) the same function computes `u(2, 0) = 21`
as written. The sibling shape for the *decreasing* parameter
([[recursive-arm-reads-outer-scrutinee]], closed) is caught by the planner
(`recursion::plan`, which tracks which parameters every visible name
depends on) and compiled by measure; a `let` bound from a parameter the
self-call passes a *different* value for is not tracked, so the structural
lowering, which compiles the recursion at the `match`, closes over the
outer `let`.

Met while writing `grind`'s round loop (`saturate` in
`lib/std/tactic/grind.hthr`, issue [[grind-e-matching]]): `let g =
close(fs0)` above `match rounds { … saturate(r, …, fs2, …) }` kept the first
round's graph, so instances were found every round and never seen. The fix
there was to put the `match` first; any library `fn` of this shape is
silently wrong.

Wanted: the planner treats a parameter the self-call does not pass through
unchanged like the decreasing one: a name bound from it above the recursive
`match` and read inside sends the declaration to the measure route (or
refuses it with the spelling that works: bind the `let` inside each arm).
Also audit the library for the shape (a `let`/`have` above a recursive
`match` reading a non-uniform parameter).

Acceptance: `u` above computes `u(1, x) = x + 11` (or is refused with the
reason), on the literal and neutral axes; `crates/elab/tests/recursion_meaning.rs`
pins it.

## Resolution (2026-11-02)

`recursion::plan` now tracks, at each recursive `match`, which parameters
its self-calls pass a different value (`varied_params`: the ones ih
generalization quantifies, and indices an indexed `match` rebinds). A name
bound **above** the `match` whose value depends on one of them, and read in
an arm, sends the declaration to the measure route like a read of the
decreasing parameter does (`RecursionPlan::ByMeasure { from, .. }`), with a
`recursion-by-measure` note naming the parameter and the structural spelling
(bind the `let` inside each arm). Where the decreasing parameter has no
measure (neither `Nat` nor `List`) it is refused with that spelling. Reading
the varied parameter itself, a `let` bound inside the arm, or one bound from
a parameter passed unchanged keeps the structural lowering.

`u` above now computes `u(2, 0) = 21` and `u(1, x) = x + 11` by `refl`, with
`u_unfold(Succ(k), x): u(Succ(k), x) = u(k, x + 10)`; `wrong` is refused by
the kernel. Pinned in `crates/elab/tests/recursion_meaning.rs` (literal and
neutral `x`, a `have` in a checking position, the self-call argument, a
`let` chain under a nested `match`, a list recursion at an open element type,
the refusal, the negative control, and the structural controls).

Not covered: a parameter whose *type* mentions a varied one (generalized by
dependency closure in `generalize::varying_params`) is not itself treated as
varied by the surface planner; a `let` bound from such a parameter alone
above the `match` would still be stale. No library code has the shape.
