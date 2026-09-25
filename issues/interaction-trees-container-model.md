---
title: Interaction trees over container events, cut at fuel: check the investigation against code
status: open
labels: [effects,semantics,design,research]
created: 2026-09-24
updated: 2026-09-24
---

Owns the follow-ups of `docs/interaction-trees-fit.md` (the 2026-09-24
investigation of Xia et al., `docs/3371119.pdf`): interaction trees with
**container events** (`Cmd : Type<l>`, `Resp : Cmd -> Type<l>`) over trees
cut off at fuel, with no kernel coinduction. The doc argues this keeps
everything at one level, needs no `Type`-indexed families, and fits
`simulate`'s `converges`/`fuel_monotone` interface; this issue owns checking
that argument against real code.

## Questions, in order

1. **The depth-indexed bisimilarity conjecture** (doc §3.7). For
   deterministic trees, does `Π n. euttₙ` (inductive Tau peeling, index
   consumed by `EqTau`/`EqVis`) coincide with the greatest fixed point?
   Pure mathematics: settle it on paper or in Coq before anything rests on
   it. If it fails, record the counterexample and what the finitary route
   then loses.
2. **The library**, once the surface can write it: `Events`, the fuel-cut
   tree, `bind`/`iter`/`mrec`, `is_trace_of` (the paper's Fig. 20, already
   inductive), trace refinement, and the bridge to
   `converges`/`fuel_monotone`. Check the doc's claim that the Fig. 5
   structural laws are definitional in this encoding.
3. **A handler**: interpret a state-event container into world threading
   (doc §6.5), to test the claim that the two leanings of
   [[effects-direction]] compose rather than compete.

Kernel coinduction (a negative `M`, doc §3) is **not** in scope; it waits
on a customer that needs liveness or concurrency.

## What it assumes from elsewhere

- **[[inductive-compiler]]** owns tier-2 (W-lowered) surface inductives.
  Assumed here: only that a recursive function-typed field (`k: Resp(c) ->
  ITree`) eventually becomes writable. Questions 2–3 wait on it; question 1
  does not.
- **[[effects-direction]]** owns the effects decision. This issue supplies
  evidence, not the verdict.
- **[[linux-syscall-trace-model]]** owns the machine trace; doc §6.1 sketches
  it as this issue's first customer.
