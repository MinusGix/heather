---
title: Specs as coalgebras over Linux's calls and answers, and the judgment Sim
status: open
labels: [native,x86,semantics,proofs]
area: heather-in-heather
milestone: [hih-pl-spec]
created: 2026-10-20
updated: 2026-10-20
---

Round P1 of `docs/native-program-logic-design.md` (§2): specifications as
coalgebras over Linux's events, and the judgment `Sim`.

## Scope

- `LinuxCmd` and `LinuxAns` (a read names its `max`), `Answers(c, a)`, and
  `Requests`/`answered` factored out of `LinuxRuns`' arms so that `LinuxRuns`
  and `RunsAs` read the same definitions.
- `Move<Q>` (`Exit`, `Call(c, k)`, `Cut`) and `Spec<Q>`; `Valid`, `trace`,
  `RunsAs` by recursion on the history; `Sim`, and that it is a
  `StepsBack` goal.
- The bridge both ways: `RunsAs(spec, q, h, s)` iff
  `LinuxRuns(trace(spec, q, h), s)`.
- One spec: the stream filter's (`filter_spec(step)`), with a lemma that
  `filter_events(…)` is its `trace` at the history the steps and ending
  encode, and `filter_prints` restated over `trace` alone (§2.5).

Library only: new module(s) beside `linux_x86_64_io`; no program or
producer moves. Touches no elaborator file.

## What it assumes from elsewhere

- **[[linux-syscall-trace-model]]** owns which calls and answers Linux has.
  Assumed here: only today's six events.
- **[[interaction-trees-container-model]]** owns trees. Assumed here:
  nothing; `Cut` is reserved for its bridge (design §7).
