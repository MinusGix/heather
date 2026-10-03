---
title: Certify plain wc: carried state across reads, a multi-field state, a three-field line
status: closed
labels: [x86,native,compiler,design]
created: 2026-09-28
updated: 2026-09-29
---

Second certified program, chosen to break the `wc -l` template
(2026-09-28 discussion): words straddle reads, so `--adds` can't be stated;
the state has four fields; the output is GNU's three-field pipe line.

Design: `docs/native-wc-design.md` (draft; §8 holds the open decisions).

Slices: A, the fold contract (library `loop_run_folds`, `--folds` replaces
`--computes`/`--adds`, `wc -l` migrates); B, record carries (reflector,
`LoopHead` placement over the register file, register budget, probe V3 first);
C, the `%7d %7d %7d\n` formatter; D, the program.

## What it assumes from elsewhere
- **[[linux-syscall-trace-model]]** owns the trace. Assumed here: only that
  `LinuxRuns` and the write loop are unchanged.
- **[[function-ir-x86-join-placement]]** owns parallel copies. Assumed here:
  nothing any more: in-place update went through a write order instead
  (design §4.6; [[native-loop-state-in-place]], closed).

## Log

- 2026-09-28: Decisions (design §8): GNU pipe format now, POSIX minimal and a proven C-style API filed as [[native-proven-formatting-api]]; slice A (fold contract) first. The register fallback stays open until probe V3.
- 2026-09-28: Slice A landed (design §3.1): library fold contract (LoopFolds, step_fold, loop_run_folds, step_fold_advances), --folds replaces --adds, --computes now states spec = fold from zero, room premise on the input length; wc -l migrated. Full suite 3085 passed. Next: slice B, probe V3 (registers) first.
- 2026-09-29: Slice B landed (design §4.5–4.8). B1 records in the reflector and near conditionals (9c3f05df); B2 carry placed over the register file (ad593863); relief 4, fields certified one at a time (ce46cd60); B3 the record-state loop (9c1b2321); B4 `lib/elf64_read_state.hthr`, the reading process over a state kept in R13 R14 R15 R8 with no copy or save, claim stated over the fold from init; the record generator adds `_rep_moves` and `_room`. Test `read_state_process` (library, refusals, wc composed). Next: slice C.
- 2026-09-29: C1 landed (5d783bff, design §5.1): `lib/field_line.hthr`, a field as two words (value above bit 32), spaces by `mark`, per-column spec; both words certify natively. V4 found the words lower to 1.9 + 2.8 KB, past the one-page image; user chose (§8.4) to lift the page limit. The lowering size is filed as [[structured-lowering-code-size]].
- 2026-09-29: C2 landed (design §5.2): page moved to 0x410000 (4418317e); `lib/elf64_write_loop.hthr` (print's write loop at an offset) and `lib/elf64_read_fields.hthr` (three-field tail over the state process, StoredList page algebra, `read_fields_runs`). wc's loop composes into the printing claim (test read_fields_process). Slice C done; next D (program, words spec, CLI profile).
- 2026-09-29: Slice D landed (design §6.1). `examples/x86-native/wc.hthr`: specs as a reader checks them (`wc_lines` a filter, `wc_words` the non-empty pieces of `wc_split`, `wc_bytes` the length) and `count_wc_input`, the fold from zero computes them (V5: checks in seconds; arithmetic through helper lemmas because of [[omega-record-projection-atoms]]). CLI `--read-loop --fields` with `--spec` ×3 (`crates/cli/src/native/read_fields.rs`), library claim `read_fields_spec_runs`, code length by `read_fields_code_len` (evaluating the 15 KB code's length ran past every rail). The loader leaves bundled module names to the builder (`load_providing`). Test `native_wc`: refused spec order, then the executable against the counts and the host's `LC_ALL=C POSIXLY_CORRECT=1 wc`. A cold build at width 1 fits the CPU rail with room. Replaying its image overflowed the main thread's stack in the test profile: builds now run on a large-stack thread ([[module-image-decode-depth-vs-stack]]). The round's success test (§1): `wc -l` is the `--read-loop` profile unchanged and `wc` is a second output shape, not a count-specific flag; `wc -l` does not yet run on the state process.
- 2026-09-29: `wc -l` moved onto the state process (design §9): the Nat loop's count placed in R13 (flag in R11), Nat-state facts and `read_count_runs` in elf64_read_state, the print tail restated at an offset in new `lib/elf64_count_print.hthr` over elf64_write_loop; the producer shares the state head and write loop across `--read-loop`, `--print`, `--fields`. The old R11-count process in elf64_read_loop and the layout-bound tail in elf64_read_print were deleted (~1650 lines); their refusal tests now target the libraries that use the pieces. The round's success test (§1) is met: `wc -l` and `wc` run on one process.
- 2026-09-29: Follow-ups filed from the round: [[closed-length-facts-evaluate-encodings]], [[native-build-no-partial-diagnostics]], [[load-providing-swallows-resolve-errors]], [[bundled-module-names-outside-build]], [[wc-fixture-duplicates-example]], [[read-profile-module-names]], [[nat-loop-generator-as-record]], [[fields-profile-shape]] (also [[omega-record-projection-atoms]], [[module-image-decode-depth-vs-stack]], [[structured-lowering-code-size]], filed earlier).
