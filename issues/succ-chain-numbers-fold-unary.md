---
title: A number written a successor at a time is folded a successor at a time
status: closed
labels: [kernel,perf]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

A number the evaluator holds as a run (`Val::NatRun`) is folded by its
algebra's class: `same`, `leb`, `sub` and `add` over two literals cost a
step or two whatever their size. A number *written a piece at a time* was
not a run, and every fold over it took a step a successor:

- `Succ(next)` evaluates to `Val::Succ` of a thunk, never a run, so a
  counter threaded through a recursion (`next`, then `Succ(next)`: the ids
  `rt_lower`'s `Tm::one_node` gives out, the label counter of an emission)
  is a chain of thunks, each forced to a successor of the one before;
- a counter read off a call's result (`lowered.next`) is the glued call
  until something eliminates it, so the chain runs through unfoldings;
- `next + k` is a run of `k` whose tail is the number before.

So comparing two ids cost their size, each time, and a function that
looks its ids up was quadratic in its node count. It was the superlinear
part of [[native-function-emission-one-statement]] and most of the
placement search's read.

## Fix

A fold whose step the run machinery iterates (`Sync` or `Affine`), meeting
a successor whose predecessor is *already forced* to a number, reads the
chain as the run it spells (`Eval::forced_run`, `crates/kernel/src/eval.rs`):
it walks the forced pieces down to the first thunk that is not a forced
number, charges a unit of fuel a piece, and re-memoizes every piece as the
run it is (`ValueArena::recache_tm`), so a piece is read once. The right
operand of a synchronous fold and a run's forced tail are read the same
way. Nothing is forced that was not: a fold that would not have looked
below a predecessor still does not. A glued call keeps its glue (its
unfolding's memo is what is rewritten), and a memo read notes a sealed
proof as a force does.

The re-memoized value denotes the same number, so the memo stays a
function of its closure; only the representation changes.

## Tests

`eval::tests::a_forced_successor_chain_folds_as_the_run_it_spells`,
`a_run_over_forced_runs_folds_as_one_run`,
`an_unforced_successor_is_folded_as_written` (fuel bounds, and that a link
is remembered); in Heather, `nat_tests::climbs_far` and
`climbs_through_far`, which run out of fuel without the reader (checked
against a kernel with it switched off).

## Not done

- A first fold over a chain that nothing has forced still forces it a
  link at a step; it is the second that reads a run.
- A fold whose step does not classify (`Opaque`) is untouched: it was a
  step a successor over a run too.
