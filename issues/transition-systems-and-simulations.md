---
title: One transition-system library: closures, invariants, simulation diagrams
status: open
labels: [relation,native,semantics]
area: mathematics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

The reflexive-transitive closure of a step relation is defined four times
with its own kit each: `Steps`/`Reaches` (`lib/std/relation/relation.hthr`),
`MachineRuns`/`MachineSteps` (`x86_64_stack`), `FetchedRuns`/`FetchedSteps`
(`x86_64_fetched_code`), `LinuxStepsN`/`LinuxSteps`/`LinuxPlus`
(`linux_x86_64_io`). Each has `refl`/`one`/`cons`/`append`/`trans`, and the
inclusions between them (`machine_runs_of_fetched`, `linux_steps_of_fetched`,
`linux_steps_of_machine`, `LinuxIo::steps_of_stack`) are separate inductions
where a generic closure gives one monotonicity lemma. About 100 citations.
`SimPaid` is a star/plus simulation diagram spelled for one tree type.
`docs/native-mathematics-survey.md` §3; survey rank 3.

## Scope

- Over any step relation: `StarN` (counted, so concatenation stays a plain
  induction), `Star`, `Plus`, their kit, and monotonicity under an
  inclusion of steps.
- Inductive invariants; determinism and its consequences.
- Simulation diagrams: lock-step, plus, and star with a well-founded measure
  (stuttering); vertical composition; a forward simulation into a
  deterministic target is a backward one.
- Restate the four machine closures as instances, keeping their names as
  definitions so clients do not change.

## Done when

The four kits are instances of one, their inclusion lemmas are
monotonicity, and two FunctionIR passes compose by diagram composition.

## What it assumes from elsewhere

- **[[itree-iter-simulation]]** and `itree_sim.hthr` own tree-side
  simulation. Assumed here: nothing; this issue is the state-side partner.
