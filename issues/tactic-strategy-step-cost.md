---
title: A Heather tactic's strategy code costs most of a run in evaluation between requests
status: open
labels: [metaprogramming,performance]
area: tactics
milestone: [tac-host-interface]
created: 2026-10-22
updated: 2026-10-22
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
