---
title: wc as a command: file operands, flags in one binary, argv and open in the process model
status: closed
labels: [native,x86,semantics,design]
area: heather-in-heather
created: 2026-10-02
updated: 2026-10-21
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

- 2026-10-03: **Designed** (`docs/archive/native-wc-command-design.md`; no code yet). The target is GNU `wc` 9.4 under `LC_ALL=C`, width rule included. That rule needs one more syscall, `newfstatat`, made for every operand up front. The flags are `-l -w -m -c`, bundles of them, `--` and `-`.
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
- 2026-10-04: **C3 built: the per-file driver** (`lib/elf64_command.hthr`, claim `command_runs` against `command_events`; corollaries `command_sends` and `command_exits` in `lib/elf64_command_output.hthr`, against `command_stdout` and `command_status`; design §10's C3 status).
    - **Layout.** Closed offsets from the entry, with the step piece and the chunk loop last, so only the step's own jumps depend on its length. Everything kept between operands is in 24 frame slots; RSP holds the fd. A file's name is measured at row time.
    - **Premises beyond §5.** `argc < 2^31` (Linux's `MAX_ARG_STRINGS`), and opened names of 1 to 4095 bytes (PATH_MAX counts the NUL).
    - **Cost.** Three declarations, each building freshly stored machine states and branching on a `match` over them in one body, dominated the module's first cold check: the prologue's store and test, the selection store and its few-operands test, and the total row's name writes. Split so the stores end at an abstract state described by a record and the branch starts from it, they became a small share. The module's cold check fell to under a quarter of its first form. It is now the largest module the command stands on, ahead of the stat pass.
    - **Test.** `crates/elab/tests/command_process.rs` composes the claim and both corollaries over any step piece `FilterFacts` holds of (no hand-written piece: the claim is stated over the facts), and checks §2's rows, the total row and the exit statuses by `refl`. `command_refusals.rs` has four refusals. Cold, the library prefix is more than one CPU rail, so `scripts/test` populates it in two bounded processes first (`semantic_command_warmup`).
    - Filed [[list-literal-left-of-append]]. Next, C4: the producer, `wc.hthr` as the command, and deleting the `Fields` finish.
- 2026-10-05: **C4 built: `wc` is the command** (`crates/cli/src/native/read_command.rs`; `examples/x86-native/wc.hthr`'s `wc_command`; design §10's C4 status). `build-x86` builds it, and `native_wc` runs §2's table and a sweep of piped inputs against the expected output and the host's `wc`. The `Fields` finish, `elf64_read_fields`, `read_fields.rs` and `read_fields_process` are deleted; [[fields-profile-shape]] is closed.
    - **Producer.** It reads the columns back from the checked context by evaluation, and the library's code bytes by evaluating `command_parts`, so no library encoder is restated in Rust.
    - **Two library changes.** `frame_at` is now `BitVec::ofNat`, bridged by `frame_counted`, because the iterated-increment form of a frame address cannot be evaluated. `layout_code_same` states a long part a piece at a time, since one declaration's fuel evaluates only a few hundred bytes.
    - **The claim.** `{p}_column{j}_means` ties each slot to its column's meaning. Joining that to `{p}_stdout` is residue ([[native-wc-command-residue]]).
    - **The test.** Cold, the command's library is more than one CPU rail, so `scripts/test` warms `target/native-test-images` in three bounded processes first (`command_filter_half_is_ready`, `command_stat_pass_is_ready`, `command_bundle_is_ready`).
    - **Cost.** Logged on [[x86-certificate-per-declaration-constant]]. The certificate is about a quarter of a cold build, and two thirds of it is the joins of four long parts.
- 2026-10-07: Reviewed after C4; the follow-ups and their order are on [[native-wc-review-follow-ups]].
- 2026-10-21: Closed as not planned: the layer it is about was burned in B1 with the hand-proved native process stack (docs/native/native-program-logic-design.md §3.1, [[native-burn-process-stack]]); the last commit with it is 189659d (tag native-v0). The rebuild states programs as interaction trees and compiles them, so this per-program work does not come back in this form.
