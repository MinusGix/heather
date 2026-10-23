---
title: A Heather tactic's strategy code costs most of a run in evaluation between requests
status: closed
labels: [metaprogramming,performance]
area: tactics
milestone: [tac-host-interface]
created: 2026-10-22
updated: 2026-10-23
---

Each request a Heather tactic makes costs one evaluation of the tree to its
next node, and for strategy code that evaluation, not the host's answer, is
the run's cost. Measured on round 3's `split_all` (2026-10-22, elaborator
and kernel at opt-level 3): the host answers a request in a negligible
share of the run; forcing the resumed tree's next node (`Interpreted::pin`'s
`fst`) is nearly all of it, and costs two to three orders of magnitude more
per request than a tight loop of the same requests
(`tactic_host::long_runs`' `spin`). The proof component (`snd`) is cheap. A
`split_all` over two booleans makes a few hundred requests, so its tests are
among the omega family's slower members.

## What is known

- Per-step cost varies with the library code the step runs (`focus` and
  `bind` layers, `blocker`'s search, `fit`), and is not a function of how
  many requests came before: the run-length chain of
  [[tactic-run-continuation-chain]] stays fixed.
- Not measured yet: which part of the force dominates (the `fit` dispatch per
  `focus` layer, `Tac::bind`'s rebuilt continuation, the tier-2 lowering's
  `elim_W` per layer, or rebuilding `List` answers with `++`).

## Possible directions

- Profile one `split_all` run (the kernel's value metrics, or a sampling
  profiler on a local machine) before changing anything.
- If `focus` dominates: answer `Goal` from a host-side focus stack
  (`Focus(goal, locals)` / `Unfocus`) instead of a Heather handler wrapping
  every later request.
- Compiled Heather tactics (design §8a tier 3) remove interpretation cost
  generally; this issue is the case for doing the cheap part sooner.

## Cause (2026-10-23)

Not the strategy's reduction: a traced request (host loop, temporary
counters) took a few hundred evaluator steps but tens of milliseconds. A
stack sample put nearly all of it in `shift_local` under
`Eval::fire_elim_w`. Every `elim_W` β built its induction hypothesis
`λ y. elim_W(…; f y)` as syntax, shifting the eliminator's whole motive and
step under three binders, and the recursive call fired on that copy, so the
next level shifted it again. `ValueArena`'s `WIhSyntax` memo (round 1) shared
the copy between recursions at the *same* depth only. `focus`, `Tac::bind`
and `attempt_from` recurse one level deeper per request they pass on, so
every request paid one fresh copy of each handler's tier-2 `match` (its every
arm, with `Tac`'s full `W` annotations) per enclosing layer. This is
[[wf-ih-rebuilt-per-node]] again, for `W`.

## Fix

`Val::WIh { elim, label, children }` holds the ih as a value, as
`Val::WfIh` does for `elim_Wf`. Applied over λ children it fires `elim` on
their body, charged the same two β the λ charged; over any other children,
and for readers that inspect it (`readback.rs`'s `w_ih`, the fold-class
probe), it is built as the λ exactly as before (`Eval::w_ih_lam`).
Conversion treats it as opaque, as it does `WfIh`. No semantic content:
`crates/kernel/tests/conv.rs`'s
`the_elim_w_ih_is_the_recursive_call_on_the_child` pins both paths, and
the readback unit test still spells the reducer's λ.

## Result

`scripts/perf ab --base origin/master`, 3 interleaved cold samples, the
`tactic_split_all.rs` theorems as one file: each `split_all` theorem −96 to
−98.6% of its time (the slowest, the conjunction, about two orders of
magnitude), every count column identical but `eval_drives` (−0.1%), peak
RSS −74%. What a cold check of that file now spends is elaborating
`lib/std/tactic.hthr` itself, chiefly the kernel gate of its handlers
(`attempt_from`, `first_of_among`, `focus`), which images cache.
