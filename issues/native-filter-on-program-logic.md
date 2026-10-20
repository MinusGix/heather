---
title: The stream filter proved through the program logic
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-first-program]
blocked-by: [native-loop-rule]
created: 2026-10-20
updated: 2026-10-20
---

Round P4 of `docs/native-program-logic-design.md` (§9): the stream filter
proved through the program logic end to end.

## Scope

- `tr` and the other filter programs' claim becomes
  `Sim(io_linux(), filter_spec(step), q0)(io_initial(…))`; the existing
  `LinuxRuns` claim is derived from it through the bridge, so tests and the
  CLI's claim instantiation can move after the library does.
- `elf64_read_filter`'s hand inductions (`filter_loop`, the `eof_from`
  instance) and its history encodings (`EofSteps`/`EofEnd` uses,
  `filter_events`) are deleted, not kept beside.
- The stdout fact comes from the spec (P1's `filter_prints`), not from the
  claim's event list.
- Executables stay byte-identical.

Touches the native support lists and `crates/cli/src/native`, a shared
hotspot (`docs/roadmap.md`, "Parallel lanes"): do not run beside another
native round.

## What it assumes from elsewhere

- **[[native-linux-spec]]**, **[[native-one-wp]]**, **[[native-loop-rule]]**
  own the logic's pieces.
- **[[native-loop-emitting-stores]]** owns the filter's program shape and
  its observable, which this round must reproduce.
