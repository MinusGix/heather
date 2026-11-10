---
title: Design native library exports: runtime fns over caller-owned memory, linked into a Rust binary
status: open
labels: [native,design,compiler,memory]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-10
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
