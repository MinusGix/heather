---
title: Fetched steps are deterministic, so a native claim's run is the run
status: closed
labels: [x86,semantics,proofs]
created: 2026-09-27
updated: 2026-09-28
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

## Log

- 2026-09-27: First proof boundary landed in the working tree (see
  `docs/native/fetched-step-determinism-design.md`). Canonical ordinary bytes have a
  unique decoded instruction; equal-length successful fetches from one memory
  and RIP return equal bytes. `Execute` outcomes for the same decoded
  instruction agree on all state components except TEST's undefined AF.
  Byte loads have a unique result for a fixed load and state, and two
  executions of a fixed emitted instruction agree on defined components.
  These lemmas kernel-check through the read-loop library; the full suite
  passed (3023 tests, 0 failures, 5 ignored). The issue
  remains open: cross-family byte selection, congruence across states that
  differ only in AF, syscall exclusion, and the universal process theorem are
  still required for acceptance.
- 2026-09-27: The AF congruence slice kernel-checks. Erasing AF from a state
  makes `SameDefinedState` an equality, and ordinary execution plus short and
  near branches commute with that erasure. Byte loads read the same byte from
  related states; word stores write the same bytes at the same address.
  `EmittedExecutes`, `FetchedStep`, and `StoreStep` now preserve the relation
  when their emitted witnesses agree. Fetch heads agree at a common address,
  and short/near branch encoders are injective through their decoders.
  Remaining: prove that the fetched bytes choose one witness across all
  emitted families, then lift step agreement through `LinuxRuns` to the
  universal claim.
- 2026-09-27: The same-length fetch result was strengthened from one state
  to two states equal on defined components. It selects the same canonical
  ordinary instruction and gives related outputs; the short branch case
  selects its control without a length assumption. The near branch case has
  the same theorem given equal lengths. All are kernel-checked. The
  cross-family selector and the near length argument remain open. Full suite:
  3023 passed, 0 failed, 5 ignored.
- 2026-09-28: Closed (docs/native/fetched-step-determinism-design.md §5–7). A prefix decoder over every step form (x86_64_step_forms) makes two fetches at one address one form whatever their lengths, which settles both the near-branch length premise and cross-family selection. Steps respect defined state; no step runs at SYSCALL. linux_x86_64_determinism: LinuxRun (a run as it happened), SameResponses, linux_runs_determine / linux_runs_every, and claim_is_run so the statement is not vacuous. Each read-loop build now writes {prefix}_runs_every at the file: every run with the history's answers made exactly the claimed events. Residue: partial runs (no divergence or stop between syscalls) go to [[linux-syscall-trace-model]].
