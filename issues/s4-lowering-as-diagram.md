---
title: S4 lowering as a simulation diagram, composed with the FunctionIR pass
status: closed
labels: [native,semantics,relation]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

S4's lowering of a schedule (`lower_nodes`, `function_ir_lower.hthr`) is
proved as an invariant over one fixed valuation (`lower_nodes_keeps`): code
that lowering returns keeps the abstract register file describing the
registers. The FunctionIR pass is a composed star diagram
([[function-ir-passes-as-diagrams]]). Restating lowering as a diagram from
leaves to x86 code makes "optimise, then lower" one `StarDiagram::compose`,
not a new proof joining two theorems.

## Scope

- x86 code as a transition system: a command list run a step at a time
  (`Pending` in `transition.hthr`, generic over any `execute_steps`), whose
  run of a block's length ends where `execute_block_normal` does.
- Lowering as a `StarDiagram` from `Leaf::Step` to the code: each node is
  answered by its emitted code run in full, as a stutter (the nodes left go
  down), so folded nodes and nodes with no code need no special case.
- Compose with `optimise_star`, and read the composite's `runs` at the end
  of the schedule.

## Done when

A theorem says the optimised schedule's lowered code ends with its final
file describing words that agree, on every live output, with what the
original schedule runs to, proved by the composite diagram's `runs`.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** owns the diagrams.
- **[[function-ir-verified-lowering]]** owns `lower_nodes` and its file
  invariant (`Node::lower_at_keeps`), which the diagram's step cites.

## Log

- 2026-11-09: Done in lib/native/function_ir/function_ir_lower_diagrams.hthr.
  `Pending<I, S>` (commands left, state) with `Pending::runs`,
  `step_det`, `done_stuck` went into transition.hthr; `BlockStep<M>` is it
  at `execute_normal`, `block_runs` its run to `execute_block_normal`.
  `lower_nodes_cons` inverts lowering one node off the front. `lower_star`
  (match `LowerMatch`: nodes pure, `meant` is what they evaluate to from the
  leaf's words and holds of them, and they lower from a file describing the
  registers to the pending code before a tail) answers every node with a
  stutter over its code. `compile_star` = `compose(optimise_star,
  lower_star)`; `List::compiled_runs` is its `runs` with determinism at the
  end (`Star::stuck_determined` with tail `Nil`). Not done: S4's
  `Region::lower` does not run the pass today (the pass feeds native
  `Stmt::emits`); a region-level corollary would add `input_file` and the
  output moves around this one, once S4 optimises. Probe:
  lib/_tests/native/function_ir/function_ir_lower_diagrams_tests.hthr (a dead
  constant dropped, the rest lowered to one MOV, `compiled_runs` at it).
