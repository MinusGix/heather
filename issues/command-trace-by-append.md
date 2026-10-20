---
title: Write the command's trace so stdout and status follow by homomorphism
status: open
labels: [native,semantics,proofs,design]
area: heather-in-heather
created: 2026-10-07
updated: 2026-10-07
---

The command's trace and its observables are four recursions over one
structure. `command_events` (the trace), `CommandHistoryOk` (well-formed
histories), `command_stdout` and `command_status` each walk parse, maybe
stat, then per operand open, reads, row and close, then the total
(`elf64_command_events.hthr:98-267`, `elf64_command_output.hthr:60-134`).
The two corollaries walk it again (`command_sends`, `command_exits`). Most of
these functions take the same six leading parameters.

The trace is written in continuation-passing style
(`rest: Bool → (Nat → BitVec(64)) → List<LinuxEvent>`) so a failed write can
end the run early. That hides the fact that `sent_to(fd, ·)` is a monoid
homomorphism from events to bytes, so every observable needs its own walk.
The equational steps in those walks are long `trans`/`cong_fn` towers
(`elf64_command_output.hthr:192-200`).

Wanted: a small trace monad (state for `failed` and the totals, events by
append, early exit) with its `bind` laws, the trace written in it, and stdout
and status each read off by one homomorphism lemma.

Acceptance: the corollary [[native-wc-command-residue]] lists as unwritten,
stdout as rows of the columns' meanings over each operand's bytes, comes out
short.

## What it assumes from elsewhere

- **[[interaction-trees-container-model]]** owns the general effect trees.
  Assumed here: only that a first-order trace monad over finite histories
  does not conflict with them (it needs no recursive function fields).
- **[[native-wc-command-residue]]** owns the missing corollary. Assumed here:
  only that it is still unwritten.
