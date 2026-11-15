---
title: One transition-system library: closures, invariants, simulation diagrams
status: closed
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
`docs/surveys/native-mathematics-survey.md` §3; survey rank 3.

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

## Log

- 2026-11-09: Built `lib/std/relation/transition.hthr`: `StarN`/`Star`/`Plus`
  and their kit (cons, snoc, append, split, cases, map, monotone);
  `Invariant`, `Restrict`, `Reachable` (least invariant); `Deterministic`,
  `Stuck`, equal-length runs end together, runs are prefixes of one another,
  stuck ends agree; `LockstepDiagram`/`PlusDiagram`/`StarDiagram` (index type
  and any order `lt`), `runs`, vertical `compose` (star: lexicographic on the
  second's index under `Plus(lt₂)`, then the first's, as CompCert), and
  `backward` into a deterministic target. relation.hthr's `Steps`/`Reaches`
  moved there as `StarN`/`Star`; `FetchedRuns`/`FetchedSteps`,
  `MachineRuns`/`MachineSteps`, `LinuxStepsN`/`LinuxSteps`/`LinuxPlus` are now
  definitions at their step, their kits one-line citations, and the four
  inclusions `StarN::monotone`/`Star::monotone` at a named step inclusion.
  Probes (lib/_tests/std/relation/transition_tests.hthr) compose a stuttering
  pass (no-ops dropped) with a lock-step one. The last "done when" — two
  FunctionIR passes composed — needs a small-step reading of a leaf first,
  so it moves to [[function-ir-passes-as-diagrams]]. Residue filed:
  [[transition-divergence-preservation]] (well-founded orders, `Forever`,
  behaviours), [[labelled-transition-systems]] (traces; `LinuxRuns` as an
  instance), [[transition-run-tactics]] (runs by evaluation, a `steps`
  tactic, invariant splits), [[transition-run-predicates-migration]]
  (`ExecuteSteps`, `Site::Runs`, `LoopRuns`, `SimPaid`).
