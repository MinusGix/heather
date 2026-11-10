---
title: Prove forward-to-backward for trace diagrams (determinate target, receptive source)
status: open
labels: [relation,semantics]
area: mathematics
milestone: [hih-passes]
created: 2026-11-10
updated: 2026-11-10
---

`lib/std/relation/labelled_transition.hthr` has trace-keeping simulation
diagrams, `Determinate` (up to a state relation and event agreement) and
`Receptive`, and the step-level backward lemmas
(`TraceStarDiagram::backward_silent`, `backward_event`). The step lemmas
take the source's event as agreeing with the target's. What a compiler
correctness theorem wants is CompCert's global result: a forward diagram
from a receptive source into a determinate target gives a backward
simulation, so every behaviour of the target is one of the source.

## Scope

- The backward simulation relation CompCert builds (its `bsim` from
  `fsim` in `Smallstep`): match a target state to the source states the
  forward diagram reaches it from, indexed by the remaining stutters.
- Receptiveness supplies the source step with the target's event when the
  environment answered otherwise; events here are single labels (an
  `Option<E>`), so CompCert's `single_events` side condition holds by
  construction.
- Behaviours: terminating runs (a final predicate) and divergence
  (`Forever` at `Silent`), with `transition.hthr`'s well-founded stutter
  order.

## Done when

A theorem turns a `TraceStarDiagram` with a receptive source, a determinate
target and a well-founded `lt` into "every terminating or diverging trace
of the target from a matched state is the source's".

## What it assumes from elsewhere

- **[[labelled-transition-systems]]** owns the labelled kit and its
  determinacy and receptiveness definitions.
