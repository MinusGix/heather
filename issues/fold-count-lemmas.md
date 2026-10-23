---
title: Library lemmas for counting folds: a count's proof is one per-byte fact
status: closed
labels: [native,stdlib,proofs]
created: 2026-10-02
updated: 2026-10-02
---

A counting stream filter proves by hand that its fold computes its spec, and
the proof is the same every time. `examples/x86-native/wc.hthr` spends about
200 of its 320 lines here:

- `wc_fold_lines` and `wc_fold_bytes` are one pattern. The step adds
  `bit(p(b))` to a field, so the fold adds `bytes.filter(p).len()`; with `p`
  constant True, it adds `bytes.len()`.
- `wc_fold_words` is a second pattern. A field that grows when a non-separator
  byte arrives outside a run, together with an in-run flag, counts the
  non-empty pieces of `bytes.split_by(sep)` ([[list-split-by]]).

Wanted: both patterns as library lemmas over `fold_bytes`, taking the step's
per-byte fact as a premise. An author then proves only that per-byte fact,
which `split_all; all_goals { bv_omega }` closes for wc's step (probe
2026-10-02: lines, bytes, words and the in-run flag each went in one line,
with no `wc_next` copy of the step and no `newline_is_space`).

Where: next to `fold_bytes` (lib/native/function_ir/function_ir_loop.hthr), or `stream_filter`.

Related: [[native-programs-read-like-programs]], [[filter-computes-from-count-facts]].

## Log

- 2026-10-02: Landed 2026-10-02 in lib/filter_program.hthr (counts_filtered, counts_len, counts_runs, counts_runs_from); design S1. Suite 3156.
