---
title: Add trace-labelled transition systems and make Linux runs an instance
status: closed
labels: [relation,semantics,native]
area: mathematics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-10
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

## Log

- 2026-11-10: Round 1 (flat kit) in lib/std/relation/labelled_transition.hthr: labelled steps at `Option<E>` with `Silent(R)` as the silent part, `StarT` with concatenation along `++`, `Determinate` up to a state relation `Same` and an event agreement `Agree` (CompCert's `match_traces`) with `StarT::determined`, `Receptive`, trace-keeping lock-step and star diagrams (`TraceAnswer`: a silent step answered as the silent diagrams answer it, an event by a target run producing exactly it) with runs and composition at `StarComposeLt`, and step-level backward lemmas. Probes in lib/_tests/std/relation/labelled_transition_tests.hthr. The global forward-to-backward theorem is filed as [[labelled-forward-to-backward]]. Still open here: Linux. `LinuxRun` fits `StarT` (exit as the last event), but `LinuxRuns` is a claim quantified over every way Linux resumes, which is the shape of `RunsAs` over itree traces; the proposed next round is a call/answer layer over itree's `Events`/`Trace` with runs and claims as its two closures, Linux and `ITree` as instances (decision put to Minus 2026-11-10).
- 2026-11-10: Round 2 (call/answer layer, Minus chose "flat kit, then call/answer layer"): lib/std/itree/call_system.hthr. `CallSystem<A, R>(E)` = silent step, stop states, returns, asks, and an answer *transformer* `answered(a, c, x, next)`; `CallSystem::Holds` reads an itree `Trace<R>(E)` against it; runs (`of_resumes`, ∃) and claims (`claiming`, ∀) are two transformers; `claim_is_run`; trees as systems (`CallSystem::tree`, `IsTrace::holds`/`tree_is_trace` both ways); `CallSystem::Refines`; determinacy `CallSystem::determined` from `Meets` (silent steps keep `Same`, stop states take no silent step, related stop states return/ask/answer alike; answers compared by `Alike` and equated as one-step traces, so no transport between response types). Linux: `RunsAs` is now literally `Holds` at `CallSystem::linux_claims` (clients unchanged), `RunsAlong` at `linux_runs`; `linux_meets` gathers the Linux facts; `runs_as_determined`; `Sim` ↔ `Refines` (`sim_refines`, `refines_sim`). `LinuxRuns`/`LinuxRun` stay lists (an empty list is False, an empty trace True, so they cannot be literal instances) and are bridged (`Trace::of_linux_events`, `linux_runs_claims`, `linux_run_along`, `linux_run_events`); `linux_runs_determine`/`linux_runs_every` moved to linux_x86_64_sim and are proved through the generic theorem; the list-specific `TailsAgree`/`call_resume`/`*_determines` are gone. Done-when met in that reading (pending Minus's call on migrating the lists, 2026-11-10). Follow-ups: [[labelled-forward-to-backward]], [[call-system-diagrams]].
