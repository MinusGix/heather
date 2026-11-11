---
title: Design native library exports: runtime fns over caller-owned memory, linked into a Rust binary
status: open
labels: [native,design,compiler,memory]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-11
---

Design round: a `runtime fn` over memory its caller owns, exported under a
named contract and linked into a Rust binary. Pieces 2, 3 and 7 of
`docs/native-lexer-crypto-roadmap.md` §2. Both of that roadmap's targets are
libraries (the lexer's scanner linked into `heather`, SHA-256's compress
linked into `crates/cache`), and nothing on master compiles a library:
`compile-x86` certifies word functions with "the platform ABI around the
code outside the proof", and `write-elf` builds closed programs whose
buffers are static slots.

A design note first (`docs/native-library-exports-design.md`), extending
`docs/compilation-vision.md` (its question 5 fixes the calling contract
between producers inside Heather; an export is that contract met from
outside). No code before Minus accepts it.

## Scope

- **One notion of buffer.** Decide with [[source-buffers-as-views]] whether a
  buffer becomes an address held in a word plus a capacity, with static,
  borrowed, arena and frame buffers as instances.
- **The unit of export.** The roadmap's lean is a `Source` procedure whose
  shared buffers are the caller's, entered through a System V shim, so a
  library is not a third pipeline. Check it against
  `native_compile_correct` and the procedures' linking theorem; say what a
  procedure with a buffer *parameter* is.
- **The contract.** A named System V subset: argument and result registers,
  stack alignment, the red zone, the direction flag, callee-saved registers
  (the bootstrap export allocates only caller-saved ones, which costs no
  proof), and each item it does not model, listed. Composed with a
  per-function footprint: the spans read, the spans written, everything
  else unchanged, over `lib/std/data/set/span_set.hthr`. The Rust caller's
  obligations (valid, disjoint spans of the stated lengths) are the
  precondition; say where they are written down on the Rust side.
- **The theorem.** `compiled_returns` grown to memory: called with spans
  holding `xs`, the code returns `f(xs)`'s words and leaves `f(xs)`'s
  buffers in the written spans. A leakage clause is left room for
  ([[native-constant-time]]).
- **Position independence.** Rust links position-independent executables.
  Lean: a constant table's base arrives as a hidden argument from the shim
  first, RIP-relative `LEA` later.
- **The artifact.** What `compile-x86` writes (assembly with certified
  bytes today; whether an object writer in Heather is worth it), symbols,
  read-only data for tables.
- **Linking and bootstrap.** `build.rs` cannot run `heather`. Lean: the
  generated assembly and a digest of its certificate are checked in, with a
  gate that regenerates both and compares bytes when the source module or
  the compiler changes; a Rust fallback stays for every host that is not
  x86-64 Linux, and as the differential oracle
  ([[native-differential-harness]]).
- **What it supersedes.** Say which of the 2026-08/09 call issues this
  round closes or absorbs, so the backlog does not grow by it.

## Done when

The note is accepted, with a negative control named for each clause of the
contract (a write outside the footprint, a clobbered callee-saved register,
a misaligned stack), and the implementation rounds filed against it.

## What it assumes from elsewhere

- **[[runtime-extern-c-abi]]** and **[[named-abi-contracts]]** own the ABI
  vocabulary. Assumed here: only that a contract is a named specification,
  never evidence.
- **[[x86-call-memory-footprints]]** and **[[wp-proved-memory-contracts]]**
  own footprints for calls and `Proved` items. This round should leave one
  notion among the three.
- **[[native-procedure-contracts]]** owns a procedure's derived contract.
- **[[self-lexer-linked]]** and **[[sha256-linked-into-cache]]** are the
  first two exports.

## Log

- 2026-11-10: The artifact and the gate exist ahead of the contract. `crates/linked` (2026-11-10): `generated/*.s` is `compile-x86`'s output, checked in, one line of `generated/EXPORTS.tsv` per export; `src/lib.rs` links each with `global_asm!` and declares it `unsafe extern "sysv64" { pub safe fn … }`, `safe` on the strength of the `_returns` theorem (the crate lifts the workspace's `unsafe_code = "forbid"` to `deny` for that one module); `crates/cli/tests/native_linked.rs` recompiles every export, compares bytes and refuses an unlisted file; `scripts/linked [--check]` rewrites. A build needs no Heather compiler. This settles the bootstrap route in practice (decision 4 of the roadmap) for functions of words. The design this issue owns is unchanged and now has a place to land: the contract for an export over caller-owned memory (what it may read and write, stated as a theorem a Rust `&[u8]`/`&mut [u32; 8]` signature can be justified by), several result words, and whether the certificate itself is checked in beside the assembly. Found by linking: `program_assembly` wrote the exported label twice when the exported function came first in the program, which the C-linked examples had never hit; fixed, with a unit test.
- 2026-11-10: Surveyed for the round after the first, looking for the shortest path to a compiled function reading the source it is lent (the scanner's loop, `lexer_tokens.hthr`'s `Accepted::longest`). It is three layers, each a round, and none is shortened by the others. (1) *The reflected language.* `rt` has `Bytes` with `Get`/`Set`/`Fold` as syntax and meaning, but the verified lowering has no case for them: a byte read is not yet a thing `Tm::lower_sound` knows ([[runtime-default-setup-soundness]], [[runtime-widths-shifts]] says the theorem must be stated over `run`, since a read observes the machine's memory and `program_eval` has none). (2) *The function compiler.* `compiled_returns` is a statement about words in and words out with the frame as the only memory, `Stack<M>` as the only law about it. Loads and stores of a lent span need a second law beside it (the span is mapped, disjoint from the frame, unchanged except where the footprint says) and the theorem restated with memory before and after. (3) *The contract*, this issue: what Rust promises about the span and where that is written down. The scanner is the cheapest first customer of all three, because it only reads: no `Set`, no footprint of writes, no aliasing question. A design that does the read half first (a borrowed read-only span, `Get` and a loop over it) gets the scanner's loop compiled and leaves the hash's state buffer as the write half. Until then the loop is Rust in `crates/linked/src/scanner.rs`, twenty lines held to the evaluated specification by probes.
- 2026-11-10: The note is written and proposed: `docs/native-library-exports-design.md`. It reverses the roadmap's lean on the unit of export: checked against the proofs, a `Source` procedure behind a shim needs the theorem `compiled_returns` already is and a second convention proved against System V, so the export is a `compile-x86` function and the verified lowering learns to read. A buffer stays a value in every meaning (`BufferLoad` over `Buffers()` unchanged) and gets a home in the lowering (the words holding base and length); addresses appear only in the machine theorem. The memory clause is one relation, `Wrote` (memory after is memory before under stores into the callee's own room), from which the caller's frame, code residency and lent spans follow; a lent span is the semantic premise `Lends`, and geometry proves it in the byte memory model. Both were probed in the kernel before writing (appendix A of the note): the definitions, five lemmas over any memory, and `DataRegion::lends`, with no new law on `Stack<M>`. Reads keep their total meaning and are lowered under a comparison the path knows. The contract's nine clauses each name what states them and a negative control; the Rust declarations become generated. Rounds R1 (the lowering reads), R2 (`rt` reads), R3 (the scanner's loop) and R4 (the write half) are in §10, landing on existing issues (§9), so no new issue is filed until Minus accepts. Four decisions are listed for Minus in §11.
- 2026-11-11: Minus's answer to the note's card (2026-11-11): "Unify first and then export." The note's memory clause, lent spans and contract stand; its rounds are re-sequenced by `docs/native-one-compiler-design.md` ([[native-one-compiler]]): R1 is U1 plus U3's lowering half, R2 is U3's `rt` half, R4 is U4, and R3 (the export itself) is E, after the program compiler and the function compiler are joined.
