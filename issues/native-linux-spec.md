---
title: Specs as coalgebras over Linux's calls and answers, and the judgment Sim
status: open
labels: [native,x86,semantics,proofs]
area: heather-in-heather
milestone: [hih-pl-spec]
created: 2026-10-20
updated: 2026-10-21
---

Round S1 of `docs/native-program-logic-design.md` (§4, §5): Linux's events as
a tree container, and the judgment `Sim` against a tree.

## Scope

- `LinuxCmd` and `LinuxAns` (a read names its `max`), `Answers(c, a)`, and
  `Requests`/`answered` factored out of `LinuxRuns`' arms so that `LinuxRuns`
  and `RunsAs` read the same definitions.
- Trees over that container from the tree library; `next(t)` (exit, call or
  cut, Taus stripped by structural recursion) as what the logic evaluates.
- `Valid`, `trace`, `RunsAs` by recursion on the history; `Sim`, and that it
  is closed backward under `LinuxSteps`.
- The bridge both ways (`RunsAs(t, h, s)` iff `LinuxRuns(trace(t, h), s)`),
  and `trace = is_trace_of`'s trace, so refinement of a tree is a lemma.
- One spec: `tr`'s tree (iter over read, fold, write), with its stdout fact
  proved about the tree alone.

Library only; touches no elaborator file and no native producer.

## What it assumes from elsewhere

- **[[interaction-trees-container-model]]** owns the tree library. Assumed
  here: container events, fuel-cut trees with `bind`/`iter`, `is_trace_of`.
- **[[linux-syscall-trace-model]]** owns which calls and answers Linux has.
  Assumed here: only today's six events.

## Log

- 2026-10-21: Unblocked: [[interaction-trees-container-model]] closed with the tree library (PRs #94, #99). Minus's decision for this round (design §10, item 1): the read is abstract from the start, "a chunk of any size the program allows", not a buffer size fixed into the spec; the machine-side `ReadCmd(fd, max)` relates to it through an `EventMap`. His standing rule for the rebuild is the ideal version from the beginning, with no cruft in core pieces.
