---
title: Certify plain wc: carried state across reads, a multi-field state, a three-field line
status: open
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
