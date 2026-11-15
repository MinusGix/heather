---
title: Let native programs load and store buffer bytes, and start with constant bytes
status: closed
labels: [native,ir,proofs,memory]
area: heather-in-heather
milestone: [hih-tools,hih-pl-source]
created: 2026-10-26
updated: 2026-10-26
---

Round 1 of `docs/native/native-real-programs-plan.md` (§3.1, §6). No native
program can look at a byte. A `Compute` leaf sees only the environment's
words (`Env::valuation`, `lib/native/native_source.hthr`), FunctionIR's
`Node` has no memory operation, and `Source::start` zeroes every buffer, so
a program can neither test its input nor put a byte it chose into its
output. This blocks 11 of the plan's 14 tools.

## Scope

- Buffers as FunctionIR state edges, the decided shape
  (`docs/native/native-effect-source-design.md` §6): `Load(out, buf, index)` and
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

## Log

- 2026-10-26: Done. `tr a-z A-Z` and `yes` are sources in `lib/native/native_tools.hthr` with no theorem of their own; `heather write-elf` builds both and `crates/cli/tests/native_tools.rs` runs them beside GNU's on random input (seeded, `HEATHER_TOOLS_SEED`), in the fast lane's SKIP. What was built, and where it differs from the scope above: (1) Minus chose to keep `eval` as it is and add `StructuredRegion::run` beside it (`function_ir_state.hthr`), threading `List<List<BitVec(8)>>`; `run_empty` proves `eval` is `run` from no buffers, and `Env::compute` runs `run`. The nodes are `BufferLoad(output, buffer, index)` and `BufferStore(output, buffer, index, value)` (Asm already owns `Load`/`Store`); the store has an output, the byte then at the index, since every node writes one port. An index at or past the buffer's length loads zero and stores nothing (`List::update` past the end is the identity). (2) The statement compiler compiles a leaf that is all pure (S4, as before) or exactly one byte node (`Prog::computes`, `Prog::single`); a leaf mixing them is refused, and a program writes each byte node as its own `ops([...])`. Splitting a mixed leaf moves to [[native-compile-wider-leaves]]. The byte code is RCX the index, a CMP against the capacity and a JAE past the access, then RBX the buffer's address plus RCX and a `LoadByte`/`StoreByte` (`Prog::byte_to`, `byte_from`); `native_compile_bytes.hthr` proves it against `Target::Placed` (`goes_byte_to`, `goes_byte_from`, `goes_loads`, `goes_stores`, `goes_computes`). (3) Initial bytes: `Buffer(capacity, initial := [])`; `Source::start` stores them one `store_byte` at a time over the zero buffers, so bytes past the capacity drop; the compiler stores them at entry a byte at a time with `StoreByte` (`Prog::inits`, `Target::goes_inits`), not a word at a time. `native_compile_correct` starts the statement induction after the entry stores. Costs seen: `write-elf` of yes (13 initial bytes) is about 2.5 min wall on the debug binary, tr about 3 min. Found: [[nested-match-on-list-tail-motive]].
