---
title: Fold programs still carry the search loop's needle through the process
status: closed
labels: [native,x86,cleanup]
created: 2026-10-01
updated: 2026-10-01
---

The read profile's programs are folds now (`read_program`'s `CountProgram`
and `FieldsProgram`, docs/automatic-author-surface-design.md §2.2). A fold step
reads no needle, but the process still carries one:

- the setup loads it into RCX (`mov rcx, 0`);
- `StateShape`, `StateJumpFacts`, the claims and the loop placement take it
  as a parameter;
- the loop generator keeps the full step's needle machinery beside the fold
  path.

Dropping it means a needle-free loop placement and state process, with the
full-step path kept only for search loops (`Break`) that do read it. Five
bytes per executable and a parameter on every claim. Worth doing when the
next process is designed (the stream filter of [[native-loop-emitting-stores]])
rather than as a refactor on its own.

## Log

- 2026-10-01: Closed by deletion (docs/native-stream-filter-design.md): every read-profile program is now a stream filter, whose process (elf64_read_filter) has no needle register, and the state process that carried it is gone.
