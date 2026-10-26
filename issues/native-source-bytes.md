---
title: Let native programs load and store buffer bytes, and start with constant bytes
status: open
labels: [native,ir,proofs,memory]
area: heather-in-heather
milestone: [hih-tools,hih-pl-source]
created: 2026-10-26
updated: 2026-10-26
---

Round 1 of `docs/native-real-programs-plan.md` (§3.1, §6). No native
program can look at a byte. A `Compute` leaf sees only the environment's
words (`Env::valuation`, `lib/native/native_source.hthr`), FunctionIR's
`Node` has no memory operation, and `Source::start` zeroes every buffer, so
a program can neither test its input nor put a byte it chose into its
output. This blocks 11 of the plan's 14 tools.

## Scope

- Buffers as FunctionIR state edges, the decided shape
  (`docs/native-effect-source-design.md` §6): `Load(out, buf, index)` and
  `Store(buf, index, value)` nodes, `eval` threading the buffers beside the
  valuation, `Env::compute` passing `env.buffers` in and out. An index past
  the buffer's length loads zero and stores nothing, as the calls clamp.
- The statement compiler lowers a leaf with byte nodes **memory-resident**,
  under S3.2's `Target::Placed`: it splits the leaf at each byte node, sends
  each pure stretch through S4 as today, and compiles the byte node with the
  `LoadByte`/`StoreByte` rules `native_compile_calls` already proves for the
  read copy. S4's `Region::lower` only refuses the new nodes. No memory
  footprint on a `Proved` contract is needed, so this does not wait on
  [[wp-proved-memory-contracts]].
- Initial buffer bytes: `Source.buffers` holds a capacity and initial bytes
  per buffer, `Source::start` fills them, and the compiler stores them at
  entry with the `WordStore` rule.

## Done when

`tr a-z A-Z` (sets fixed at build) and `yes` (fixed string) are built by
`heather write-elf` with no per-program proof and match GNU on random input
(a test beside `crates/cli/tests/native_cat.rs`).

## What it assumes from elsewhere

- **[[function-ir-buffer-state-edges]]** is the design this round builds.
  This round takes its scope, minus the S4 footprint, which moves to
  [[native-compiled-code-shape]].
- **[[native-effect-source-compiler]]** owns the compiler and
  `native_compile_correct`, which this round extends by cases.
