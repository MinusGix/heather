---
title: Move the command's remaining phases and the process libraries onto Runs
status: open
labels: [native,x86,proofs]
created: 2026-10-10
updated: 2026-10-15
---

The command's remaining hand-threaded phases and the other process libraries,
moved onto `Runs` (`docs/native-runs-design.md`, `lib/elf64_runs.hthr`).

- **The command** (`lib/elf64_command.hthr`): the row's tail
  (`named_runs`, `unnamed_runs`), whose byte stores change the page that
  `Framed` holds fixed (a `StoreByte` item carrying the page,
  `docs/native-straight-runs-design.md` "Not yet"), and `init_runs`, which
  as one stretch cost more than its chain and needs splitting at its labels.
  `inputs_runs` only composes other phases.
- **The process libraries**: formatter, scan, cursor, stat pass and row
  writer, and their frame records (`FmtKept`, `WriteKept`, `CursorKept`,
  `StatCarried`) restated over `Keeps`/`SlotsKeep`.
- **The list layouts** left in `elf64_read_pieces`, `elf64_read_filter` and
  `elf64_count_print` (`layout_code`/`layout_at`), onto `x86_64_asm` labels
  with their proofs.

Acceptance: each moved phase checks in no more kernel steps cold than
before; `build-x86` of wc writes the same bytes.

## What it assumes from elsewhere

- **[[native-straight-code-triples]]** (closed) owns the rules. Assumed
  here: only `lib/elf64_runs.hthr` and the command's frame rules as landed.
- **[[native-symbolic-execution-step]]** owns generating these chains.
  Assumed here: nothing; this work is by hand and is what that step would
  emit.

## Log

- 2026-10-10: **Five phases moved onto `cmd_straight` instead** ([[native-symbolic-execution-step]], `docs/native-straight-runs-design.md`): `loop_last` (absorbing `cursor_store_runs`, `last_tested_runs`, `last_test_block`), `operand_head`, `stdin_path`, `open_back` and `failed_runs`. Their `Runs` chains are now one call each, which states no middle predicate. `closes_runs` stays on the rules: a system call ends a stretch, and its JCCs sit on both sides of the call. The phases this issue lists as not yet moved are unchanged.
- 2026-10-15: **The dash test and `open_path` moved onto `cmd_straight`**, with a `LoadByte(ByteLoad)` item in `x86_64_asm` that `Straight` reads (`ByteThen`: the caller names the byte and its address, read under every frame). The dash test is two stretches (`dash_test`, three items; `dash_ahead`, four) with the name's case analysis in small lemmas (`first_byte`, `stdin_of_*`): cold, its kernel steps fell to well under half the hand-threaded proof's. A first draft, one seven-item stretch per case of the name, took more steps than the hand-threaded proof; `docs/native-straight-runs-design.md` ("Where a stretch forks on data, split it"). `StdinAt`/`OpenAt` take a framed state, so neither closes over the starting frame. wc's bytes are unchanged.
- 2026-10-15: **The name's scan and write, the read's failure and the loop's cursor moved onto `cmd_straight`**, once their continuations took a frame: `name_scan` (one five-item stretch per byte, over `NameReads`/`NameFound`), `name_send` (two stretches, ending in a `FramedWrite`), `read_failed` and `loop_cursor` (continuation-passing, ending in a `CursorGoes`). Cold, each phase's kernel steps fell, by about half (`loop_cursor`) to four fifths (`name_scan`, `read_failed`); the elaborator's weak-head time on each rose from milliseconds to seconds, the trade the earlier moves made ([[elab-whnf-copies-straight-continuations]]). `init_runs` as one twenty-one-item stretch took more than twice its chain's steps and was left as it was. wc's bytes are unchanged.
