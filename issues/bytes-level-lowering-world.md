---
title: The bytes level's system calls and exit lowered: the going and exited clauses of Site::Meets
status: open
labels: [native,x86,linux,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Item 7 of [[bytes-level-lowering]]: the world. The `Sys` node's step lemma for `read` and `write` (for every answer and resumption the Linux model allows; a failed read leaves its window undefined, which `Injected::undefined_change` absorbs), `Exit`, and the going and exited clauses of `Site::Meets` (`lib/std/arch/x86_64/x86_64_call_contract.hthr`). `EmitsBy` is a claim about machine steps (`Site::Moves`); a system call needs the claim form `Site::Performs`, so a region holding one is proved in that form, the regions without one lifted into it.

## Done when

`Site::Meets` in all three clauses for every routine of every program the lowering returns; the language's world probes (`echo_*`, `failed_read_undefines`, `exits`) compiled with their theorems.

## What it assumes from elsewhere

- **[[bytes-level-lowering-routines]]** owns the done clause. Assumed: it is proved for programs without system calls.

## Log

- 2026-11-25: Partial (branch `claude/bytes-level-lowering-routines`), after [[bytes-level-lowering-routines]] and [[bytes-level-lowering-loops]] closed. **Proved: the exited clause, `Site::MeetsExited`, for every program `Program::lower` returns (`lower_program_meets_exited`), vacuously: no `Exit` or `Sys` is lowered (`Body::fresh` refuses them), so the meaning never exits (`program_no_exit`, by induction on fuel; `Body::run_no_exit`, `loop_run_no_exit`).** Probes: `countdown_meets_exited`; control `exits_refused`.

  What remains, exactly:

  1. **The system call is blocked at the generic theorems, not here.** A `Sys` node's step is a claim in `Site::Performs` form (steps to a SYSCALL that `LinuxRequests` reads, then from every resumption `LinuxResumes` allows). But `EmitsBy`, `may_emit_by_seq`, `branch_emits_by`, `call_step_by`, `File::emit_call_steps_by`, `function_runs_by` and `Site::loop_iterates` are all stated over `Site::Moves` (machine steps only). So a region holding a system call cannot be composed by them as stated, nor can a routine calling one that does: the callee's contract `Site::Returns` is a `Moves`-shaped claim too. By the round's rule this is a generalisation at their source (`function_ir_lower_calls`, `x86_64_stack_runs`): e.g. `EmitsBy` over a claim form `site.Claims(writes, from, to, pre, post)` that is `Moves` or `Performs`, with `moves_trans`'s analogue for `Performs` (a run to a call, then from every resumption, a run again). Not started; the coordinator's call.
  2. **The `Sys` node itself**: code (the number in RAX, the descriptor, the window's address and the count in RDI, RSI, RDX, SYSCALL, the answer from RAX), its step lemma for every answer and resumption the Linux model allows (RCX and R11 clobbered; a failed read's junk absorbed by `Injected::undefined_change` and `Piece::undefined`), and the bridge from `SysCall::run` to its facts at the valuation (the scope check: a `Sys` binds its `result` word).
  3. **The going clause, even without system calls.** `Site::MeetsGoing` is a statement about every `Running` reachable by `Site::Step` before the return, including on runs that never return (a loop at every fuel `Going`). Every theorem so far is existential (a run reaches the post). It needs an invariant over all reachable states: for code with no SYSCALL, that every reachable state before the return is on the code's run, so no system call is made and the world stays `io` (whose history the meaning reaches at fuel 0, `Going(io)`). That wants the machine's determinism (`Site::Step` over a fetched step) and the code's control staying within its labels, which the region theorems do not state. With system calls, each reachable world must also be matched to the meaning's history at some fuel, by the same induction as the done clause.

  Verified with the rest of the branch: see the round's final `scripts/test --pr` line in [[bytes-level-lowering-loops]] and below.
