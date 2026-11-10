---
title: Carry call-system claims through simulation diagrams
status: open
labels: [relation,semantics,itree]
area: mathematics
milestone: [hih-passes]
created: 2026-11-10
updated: 2026-11-10
---

`lib/std/itree/call_system.hthr` reads processes and trees as call systems
(`CallSystem::Holds` over itree traces, runs and claims as two answer
transformers, `CallSystem::determined`, `CallSystem::Refines`), and
`lib/std/relation/labelled_transition.hthr` has trace-keeping diagrams
for systems with plain labels. A compiler pass over a calling program
(a `runtime fn` with `Io`, FunctionIR with `Invoke`) needs the two
together: a diagram between call systems that keeps what a trace says.

## Scope

- A star diagram between call systems: silent steps as in
  `transition.hthr`, stop states matched to stop states, returns and asks
  read alike, and an answered call's resumptions matched (every target
  resumption for a claim, some for a run).
- `Holds` carried through it: a claim of the source's trace from a matched
  state is one of the target's, so `Refines` composes with a pass.
- The flat view: a call system's run as a labelled system over
  `Option<Σ c, Resp(c)>`-style labels, so `TraceStarDiagram` applies where
  the answer transformer is a relation.

## Done when

A pass proved as a call-system diagram turns `Sim(io, t, s)`-shaped claims
of its source into claims of its target, with a probe at a small system.

## What it assumes from elsewhere

- **[[labelled-transition-systems]]** owns the call/answer layer and the
  flat kit.
