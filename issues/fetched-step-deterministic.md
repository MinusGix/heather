---
title: Fetched steps are deterministic, so a native claim's run is the run
status: open
labels: [x86,semantics,proofs]
created: 2026-09-27
updated: 2026-09-27
---

The native process claims (`read_loop_runs`, `read_print_runs`) are
existential: a run with the stated trace exists. For the programs the native
compiler writes, that run is the run, because each fetched step is decoded
from bytes with a unique decoding and executes as a function of the state.
Nothing states this yet. Decided 2026-09-27, with the user, as its own round,
separate from the failure paths ([[linux-syscall-trace-model]]).

## Shape of a fix

- A uniqueness theorem for `FetchedStep`: two fetched steps from one state
  reach the same state. It needs decoding to be unique on the supported byte
  forms, which the decoders' completeness proofs nearly state, and execution
  to be a function, which it is except for the `Execute` relation's undefined
  AF (the TEST rule admits both values). Either state AF in the uniqueness up
  to flags nothing reads, or fix it.
- A store step (`StoreStep`) and the syscall rules (RCX and R11 are
  quantified) have the same issue. The claim becomes "every run meets these
  events, up to the quantified registers".

## Acceptance

- `read_print_runs`'s conclusion can be restated as: every run from
  `io_initial` that follows the history's responses produces
  `eof_events(…)`.
