---
title: Certify plain wc: carried state across reads, a multi-field state, a three-field line
status: open
labels: [x86,native,compiler,design]
created: 2026-09-28
updated: 2026-09-28
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
  only that in-place state update would need it (relief 4).

## Log

- 2026-09-28: Decisions (design §8): GNU pipe format now, POSIX minimal and a proven C-style API filed as [[native-proven-formatting-api]]; slice A (fold contract) first. The register fallback stays open until probe V3.
- 2026-09-28: Slice A landed (design §3.1): library fold contract (LoopFolds, step_fold, loop_run_folds, step_fold_advances), --folds replaces --adds, --computes now states spec = fold from zero, room premise on the input length; wc -l migrated. Full suite 3085 passed. Next: slice B, probe V3 (registers) first.
