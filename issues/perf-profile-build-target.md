---
title: A one-command frame-pointer build and module-scoped perf attach
status: open
labels: [tooling,performance,kernel,elaboration]
created: 2026-09-06
updated: 2026-09-06
---

The 2026-09-06 x86 kernel round ([[function-ir-x86-proof-scaling]]) got its
attribution from two improvised pieces that are worth keeping as tooling:

1. A frame-pointer build in its own target directory
   (`CARGO_TARGET_DIR=/tmp/heather-fp-target RUSTFLAGS=-Cforce-frame-pointers=yes`,
   with `--features value-metrics`). perf's DWARF unwinding produced no
   usable stacks on the ordinary dev build; frame pointers did, at no
   measurable cost. Rebuilding it by hand each time is the friction.
2. Attaching `perf record -p <pid>` from inside the process around one
   module check (`HEATHER_FUNCTION_IR_X86_PERF` in
   `crates/elab/tests/function_ir_x86.rs`), because the base library's
   replay is most of a test binary's wall and a whole-process profile is
   dominated by it. Filtering by time is fragile; attaching by phase is
   exact.
3. A stack folder that keeps only kernel frames and prints the first five
   and last three of each path with counts (`fold.py`, scratch): the
   `ty_root > ty_w > ty_nf …` signature was visible in that output and in
   no perf report view.

## Shape

- `scripts/perf <cargo test args…>`: builds into `target/perf` with frame
  pointers and `value-metrics`, runs the given test/binary under
  `perf record -g`, and prints the folded kernel-path summary. Same ulimit
  discipline as `scripts/test`.
- Generalize the attach hook to the elaborator (`HEATHER_PERF_ATTACH=<file>`
  around `elab_module_source` / one `heather check` module), so any test or
  CLI run can profile one phase.
- Keep the `Tc::conv_ty` miss sampler the round used (bucket by head pair,
  total ns, exact first-difference excerpt) behind the `value-metrics`
  feature rather than re-inventing it: it found both the `0 ⊔ 0` level
  spelling and the three-way inductive spellings in minutes.

## What it assumes from elsewhere

- **[[perf-tracking-consistent-environment]]** owns where numbers come
  from; this is only how a profile is taken.

## Log

- 2026-09-06: Item 3 of the shape is landed, by the [[inductive-spelling-codes-nonrecursive]] round: the Tc::conv_ty miss sampler lives in crates/kernel/src/typing.rs behind the value-metrics feature (every query past the syntactic shortcut and the gate memo is bucketed by (expected head, inferred head) — El split into named-code, code-literal and other — with count, total wall ns, and an exact write_exact first-difference excerpt of each bucket's first miss, rendering capped at 8 MB a side). The table hangs off ValueMetrics (conv_miss_report; reset clears it), Elaborator::value_conv_miss_report exposes it, and the x86 scaling rail prints it under HEATHER_FUNCTION_IR_X86_VALUE_METRICS=1 with --features value-metrics. Items 1 and 2 (scripts/perf, the generalized attach hook) are still open.
