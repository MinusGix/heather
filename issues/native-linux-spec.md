---
title: Specs as coalgebras over Linux's calls and answers, and the judgment Sim
status: closed
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
- 2026-10-21: landed (S1). What it is, and where it departs from the design:
  - `lib/std/os/linux/linux_calls.hthr` (machine-free): `LinuxCmd<Size>` with `Resp`
    (the design's `LinuxAns` is `c.Resp()`, one result type per kind) and
    `LinuxCmd::Answers`; `LinuxEvent` is now `CallEvent(c, a) | ExitEvent`,
    so a run is a list of answered calls, and `sent_to`/`received_from`
    read `LinuxCmd::sent`/`received`.
  - **A read's size is abstract in specs** (Minus, 2026-10-21: don't fix the
    buffer size into the spec). `Size = Nat` is Linux's own call, which names
    `max`; `Size = True` is a spec that doesn't care which chunks its input
    comes in. `ITree::Implements` (in `lib/std/os/linux/linux_trees.hthr`) relates them:
    every Linux-valid trace of the program asks for at least one byte and
    forgets to a trace of the spec. `ITree::sized(max, t)` implements `t`
    for any `0 < max` (`ITree::implements_sized`).
  - `lib/std/os/linux/linux_x86_64_io.hthr`: `LinuxAsks`/`LinuxBuffers`/`LinuxRequests`,
    `LinuxLeaves`/`linux_answered`/`LinuxResumes`/`LinuxAnswered`,
    `LinuxExits` are the one reading of a call, and `LinuxRuns` is stated in
    them; the per-kind `linux_runs_read/…` theorems are gone (one
    `linux_runs_call`). Determinism (`linux_runs_determine`,
    `linux_runs_every`) is re-proved over the new events.
  - `ITree::next` (`lib/std/itree/itree.hthr`) and `Trace::Returns`/`ReturnsWith`
    (`lib/std/itree/itree_trace.hthr`).
  - `lib/std/os/linux/linux_x86_64_sim.hthr`: **`RunsAs` recurses on the `Trace`**, not on
    a history list plus `trace(t, h)`: the tree library's traces already are
    the histories, so `Valid`/`trace` became `Trace::LinuxValid` and the
    library's `IsTrace`. `Sim(t)(s)` = every Linux-valid trace of `t` runs as
    `s`; `sim_back` (closed under `LinuxSteps`), `sim_cut`/`sim_tau`/
    `sim_ret`/`sim_vis`, `sim_of_next`, `SimProgram` and
    `Program::sim_refines`. Bridge: `runs_as_linux_runs` (a returned trace's
    `RunsAs` is `LinuxRuns` of its events) and `linux_runs_runs_as`;
    `sim_every_run`/`sim_run_sends` read a machine's stdout off the tree.
  - `lib/native/stream_filter_spec.hthr`: `filter_spec` (read, map, write until all
    is written, at `Size = True`), `tr_spec(f)`, and `tr_sends`: on every
    returned trace, stdout is stdin mapped by `f`. Client:
    `docs/showcase/linux_spec_client.hthr` (down to a machine's run).
  - Tests: `crates/elab/tests/linux_spec.rs` (closure, kit, negative
    controls); `linux_determinism.rs`' mutations moved to the new arms.
  - Left: [[linux-sim-every-machine-run]] (the converse: a machine that
    simulates a tree makes only its traces; divergence) and
    [[linux-sized-program]] (`ITree::sized` as a `Program`).
