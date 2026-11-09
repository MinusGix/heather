---
title: Build runs by evaluation and a steps tactic over transition systems
status: open
labels: [tactics,relation,native]
area: tactics
milestone: [tac-general]
created: 2026-11-09
updated: 2026-11-09
---

Native proofs build runs by hand: a chain of `linux_steps_trans`,
`machine_steps_one`, `Star::cons`, … with every intermediate state written
out. `lib/std/relation/transition.hthr` gives these one kit; the next
saving is not writing the chain.

## Scope

- **Runs by evaluation.** For a step that is a function (`step: A → A`
  with `R(a, step(a))`), `StarN::iterate`: `StarN(R, n, a, iterate(step,
  n, a))`, so a closed run is `refl` on its end state, as closed asm facts
  are proved by evaluation (docs/proof-patterns.md). Then a deterministic system's run
  between closed states is decided, not built.
- **A `steps` tactic.** Close `Star(R, a, b)`/`Plus`/`StarN` goals from
  step rules in scope: split at the states the rules' conclusions name,
  chain them with `Star::trans`/`Plus::trans_star`, and leave the side
  conditions as goals. A registry of step rules per relation, like the
  sets tactic's operations (`SetOpEntry`).
- **Invariants by search.** `Invariant(R, P)` for a step that is a sum of
  forms (`MachineStep` is three) is one obligation per form; generate them
  (`Invariant::or` over a step that is `∨`), and let `grind` take each.
- **Diagram obligations.** For a `StarDiagram` over a step that is a sum,
  the same split: one obligation per source form, with `Answers` reduced
  to the case the user names.

## Done when

The native runs cited most (`linux_steps_trans` chains in
`native_compile_frames`, `x86_64_asm_runs`) shrink to one call each, and
one native invariant is proved by the split.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** owns the kit. Assumed here:
  `StarN`/`Star`/`Plus`, `Invariant`, `StarDiagram`.
- **[[grind-port]]** owns `grind`.

## Log

- 2026-11-09: Measured before starting: hand run chains are rare now that native goes through the compiler (linux_steps_trans 9 uses, fetched_steps_one 14, machine_steps_trans 4, linux_plus_back 3 across lib). A `steps` tactic pays little until hand-proved runs return; runs by evaluation needs a step that is a function, which native's relational steps are not. Lowered priority.
