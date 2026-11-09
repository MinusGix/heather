---
title: State FunctionIR passes as simulation diagrams and compose them
status: closed
labels: [native,semantics,relation]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

A FunctionIR pass is proved today as an equation about running a whole
leaf (`List::optimised_runs` in `function_ir_pass.hthr`): from any
valuation and buffers, the optimised nodes run to the same buffers and live
words. Two such passes chain by rewriting one equation into the next, so a
chain of passes is a new proof each time. [[transition-systems-and-simulations]]
built the diagrams that make the chain a composition instead
(`lib/std/relation/transition.hthr`: `LockstepDiagram`, `PlusDiagram`,
`StarDiagram`, their `compose`, and `StarDiagram::runs`).

## Scope

- A small-step reading of a leaf: a state is the schedule still to run with
  the valuation and buffers, and a step runs one node. Prove it agrees with
  the existing whole-leaf evaluation (one `StarN` run of the schedule's
  length ends where `run` does), so nothing downstream changes.
- Constant folding as a `LockstepDiagram` (a folded node is one step of
  the target from a matched state; match = same buffers, and the target's
  valuation agrees with the source's on every word the facts so far cover).
- Dead-node removal as a `StarDiagram`: a dropped node is a stutter whose
  index is the count of nodes left, so `lt` is `Succ(i) = j`; match = same
  buffers and agreement on the words still live.
- The pair composed by `StarDiagram::compose`, and `optimised_runs`
  recovered from `StarDiagram::runs` at the end state.

## Done when

`optimised_runs` (or its successor) is the composite diagram's `runs`, and
adding a third pass is one more `compose`, not a new run proof.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** owns the diagrams. Assumed
  here: they are stated over any step relation and index order.
- **[[function-ir-pass-arithmetic-folds]]** owns which folds exist.

## Log

- 2026-11-09: Done in lib/native/function_ir/function_ir_pass_diagrams.hthr.
  `Leaf` (schedule left, words, buffers) with `Leaf::Step` running the first
  node; `List::leaf_runs` (a run of the schedule's length ends at
  `run_nodes`) and `List::leaf_ends` (determinism: every run to an empty
  schedule ends there). `fold_lockstep` (match: folded under facts that hold,
  same words and buffers) and `prune_star` (a dropped node stutters with the
  index the nodes left; match: pruned, same buffers, words agree where the
  target still needs them), composed by `StarDiagram::compose` as
  `optimise_star`. `List::optimised_runs` moved there and is now
  `StarDiagram::runs` of the composite read at the end of the schedule;
  function_ir_pass's whole-schedule inductions `folded_runs` and
  `pruned_runs` are gone. native_compile_pass cites it unchanged.
