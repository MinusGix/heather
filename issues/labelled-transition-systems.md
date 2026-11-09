---
title: Add trace-labelled transition systems and make Linux runs an instance
status: open
labels: [relation,semantics,native]
area: mathematics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/relation/transition.hthr` is about silent steps. A process's run
is not: `LinuxRuns`/`LinuxRun` (`linux_x86_64_io`,
`linux_x86_64_determinism`) interleave runs of silent `LinuxStep`s with
syscall events, and `linux_runs_determine` is a determinism theorem
spelled for that one trace type. A labelled layer would let these become
instances the way the silent closures did.

## Scope

- Labelled steps `R: A → Option<E> → A → Type` (or `A → List<E> → A →
  Type`, CompCert's trace-labelled `step`), the silent part as an
  instance of `StarN`, and a trace closure `StarT(R, events, a, b)` with
  concatenation along `++`.
- Determinism of a labelled system up to the environment's answers
  (CompCert's `determinate`: two steps from one state with matching event
  shapes end together), and receptiveness; their run consequences.
- Simulation diagrams that preserve traces, their composition, and the
  forward-to-backward theorem for a determinate target and a receptive
  source.
- Restate `LinuxRuns` as `StarT` at the Linux step with events, keeping the
  name as a definition, and `linux_runs_determine` as the generic theorem.

## Done when

`LinuxRuns` and `linux_runs_determine` are instances, and a trace-keeping
diagram composes like the silent ones.

## What it assumes from elsewhere

- **[[transition-systems-and-simulations]]** owns the silent closures and
  diagrams. Assumed here: `StarN`/`Star`/`Plus` and the three diagrams.
- **[[linux-syscall-trace-model]]** owns which events a Linux run has.
