---
title: wc as a command: file operands, flags in one binary, argv and open in the process model
status: open
labels: [native,x86,semantics,design]
created: 2026-10-02
updated: 2026-10-02
---

The certified `wc` reads stdin only. A normal `wc`:
- takes file operands (`wc a b`, with a total line);
- takes `-l`, `-w`, `-c` in one binary (today `wc_l` is a separate program
  and filter);
- prints counts of any size (the `%7d` tail is limited to below 10^7,
  [[native-proven-formatting-api]]).

What it needs:
- **argv on the initial stack** in the process model: `argc` and `argv`
  pointers and the strings, as the ELF entry state.
- **open/close (openat) and reading from a returned fd**, as syscall events
  with failure responses (ENOENT, EACCES, which GNU reports and continues
  past).
- **A run over several inputs**: the stream filter per file, plus a total.
- **Flags** as a program-level choice of which counts to print, which is a
  finish chosen at run time.

This is a capability round of its own, after the author-ergonomics round
([[native-programs-read-like-programs]]). It owns the design. The trace
model's general questions stay with [[linux-syscall-trace-model]]. Assumed
from there: only that events carry responses and claims quantify over
histories.
