---
title: wc as a command: file operands, flags in one binary, argv and open in the process model
status: open
labels: [native,x86,semantics,design]
created: 2026-10-02
updated: 2026-10-03
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

## Log

- 2026-10-03: **Designed** (`docs/native-wc-command-design.md`; no code yet). The target is GNU `wc` 9.4 under `LC_ALL=C`, width rule included. That rule needs one more syscall, `newfstatat`, made for every operand up front. The flags are `-l -w -m -c`, bundles of them, `--` and `-`.
    - **Model (C1).** argv is read from the initial stack (`ArgvAt`, quantified over its layout). `IoMemory` gains a second RW page, `frame`, and a read-only `rest`. There is a new `WordLoad` form. Open, close and stat become events with failure responses. `eof_run` takes the fd and a continuation for a failed read.
    - **Process (C2–C3).** Nothing outlives an operand in a register: the read loop uses all fifteen. Between operands everything lives in the frame. The filter's loop and step piece and the write loop are reused as they stand. The name is written straight from argv. Columns are a table, and the row loop is library code.
    - **Formatter.** `%*d` for any 64-bit count is one hand-proved library loop (table of powers of ten, repeated subtraction). It is not generated. `Fields` goes when `wc` migrates (C4).
    - **Cost estimate** (§9, from a cold `--timings` build of today's `wc`): the generated `%7d` certificates are 47% of a cold build and disappear. The new library is about 630 declarations and +14 to +20 points, priced by kind. The driver is the uncertain line. A cold build of the full `wc` comes to about 70–80% of today's; a warm build about a tenth dearer.
    - Decisions taken by default (§11): GNU's output; no stderr diagnostics; exit at once on a failed write; the formatter as library code; `Fields` retired. Residue: [[native-wc-command-residue]].
