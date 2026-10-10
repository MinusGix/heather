---
title: Move the command's remaining phases and the process libraries onto Runs
status: open
labels: [native,x86,proofs]
created: 2026-10-10
updated: 2026-10-10
---

The command's remaining hand-threaded phases and the other process libraries,
moved onto `Runs` (`docs/native-runs-design.md`, `lib/elf64_runs.hthr`).

- **The command** (`lib/elf64_command.hthr`): the dash and ahead tests
  (`ByteTested`, `jne_open`, `dash_second`, `dash_test`), `open_path`, the
  row's tail (`named_runs`, `unnamed_runs`), `name_scan`, `name_send`,
  `init_runs`, `inputs_runs`, `read_failed`, `loop_cursor`. The row's
  writes are stated over one image (`WriteGoes(with_frame(file, frame), …)`),
  so their continuations close over the starting frame; `Framed`'s witness
  is a fresh frame, so those continuations have to take a frame (as
  `LoopGoes` and `ReadsGoes` already do) before their phases can move.
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
