---
title: wc as a command: file operands, flags in one binary, argv and open in the process model
status: open
labels: [native,x86,semantics,design]
created: 2026-10-02
updated: 2026-10-04
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
- 2026-10-04: **Probes V4 and V5 run (design §10.1); both hold.**
    - **V4.** `eof_run` takes the fd and a failed-read continuation; the driver takes the continuation as `EofProcess.fails` and needs only the EINTR half of a failure tail (`RetryTail`). The filter keeps its trace. A cold `wc` build gives the same binary with identical counters in the formatter, step piece and program proofs; the whole build is +0.11% steps, all in `elf64_read_pieces`. The head still reads fd 0 until `WordLoad` lands.
    - **V5.** One `emit` digit (`probes/wc_command/digit_emit.hthr`, no table read) is about 2.2× `elf64_write_loop`'s module time. That puts each library loop at the top of §9.3's band, so the loops may come to 10–12 points instead of 6–10. The cold-build estimate still lands under today's.
    - The per-operand driver itself is still unmeasured: V4 shows its hook into the read driver is cheap, not what composing the row, close and totals costs. Measure it at C3.
- 2026-10-04: **Formatter built** (`lib/elf64_format_width.hthr`, claim `format_runs`; design §7's status note). `%*d` for any 64-bit count and any width, proved once against `pad_left(width, ' ', decimal(n))`. Built as unrolled position-independent place blocks with immediates rather than a table loop, so it needs no `WordLoad` and stays off C1's model work. Tests: `crates/elab/tests/format_width_process.rs` (a client placing it past any header; six code mutations each refused by the kernel). `Fields` stays until C4.
- 2026-10-04: **C1 built: the model** (design §10's C1 status). `WordLoad` (any base, decoded beside the stores, determinism kept). `frame` and `rest` sit in the file's image (`IoImage`), so the read driver keeps the frame across reads without new obligations. `ArgvAt` names stack words by slot. Open, close and stat are events, with intros and determinism cases. The read head takes its fd from an `FdSource`, and a command keeps its fd in RSP rather than loading it from the frame. Stdin filters keep their traces; tr and wc -l build and run. Hand test: `crates/elab/tests/open_read_close_process.rs` (open argv[1], read to end of file, close; four refusals).
- 2026-10-04: **C2 started: the argument scan** (`lib/elf64_arg_scan.hthr`, claim `scan_runs`; spec `lib/command_program.hthr`'s `parse_args`; design §10's C2 status). Registers only, selection as a word of column bits, eight fixed letter slots. `ArgvFrom` now says argument pointers are not null, so the scan stops at the null word. Splitting the per-argument proof at abstract states took it from dominating the module's cold time to a small share of it. Test: `crates/elab/tests/arg_scan_process.rs`. Stat pass and row writer next.
- 2026-10-04: **C2's stat pass and width built** (`lib/elf64_operand_cursor.hthr`, claim `cursor_runs`; `lib/elf64_stat_width.hthr`, claim `stat_runs`; spec `command_program`'s `operands_from` and `stat_width`; design §10's C2 status). A shared operand cursor re-walks argv for the stat pass and, next, the driver; argv's pointers are named once for every page, since stats and reads overwrite it. The width ends in RSI, counted with the formatter's own digit blocks. §2's width rule is corrected: a failed first stat does not force width 1 (`wc nosuch big` pads to big's size, checked on coreutils 9.4). Test: `crates/elab/tests/stat_width_process.rs`. Filed [[elab-accepts-conjunction-for-equation]] (a kernel-only refusal that cost a bisection). Row writer next.
- 2026-10-04: **C2 finished: the row writer** (`lib/elf64_row_fields.hthr`, claim `row_runs`; spec `command_program`'s `row_counts`; design §10's C2 status). The selected columns' counts, padded to the width with a space between them, stored at the cursor by one formatter in a loop over the eight slots. It writes only the counts; the driver adds the name and the newline. The counts are words by slot at an address the caller passes, so the same code writes the total row. Test: `crates/elab/tests/row_fields_process.rs`. The per-file driver (C3) is next.
