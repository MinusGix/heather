---
title: The linked SHA-256 is two orders of magnitude slower than the cache's hash
status: open
labels: [native,crypto,performance]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-14
updated: 2026-11-14
---

The linked hash is proved ([[sha256-linked-into-cache]], `Sha256::linked_digest`).
What stands between it and the cache is its speed, measured here for the
first time.

## Measured

2026-11-14, four-core cloud box, release build, one thread, a throwaway
example over `heather_linked::sha256::stream` (not committed):

- 4 MiB in one `update`: about 6.5 MB/s. The `sha2` crate on the same
  bytes, which uses the CPU's SHA instructions as `crates/cache` does where
  it can: about 1,400 MB/s. The ratio is about 200.
- By block: `sha256_compress` alone is about 9.5 µs a block, `sha256_update`
  about 10.5 µs a block. So the compression is nine tenths of it and the
  byte-at-a-time filling one tenth.
- At a clock near 3 GHz that is roughly 28,000 cycles a block, some 250 a
  round or a schedule word. A plain scalar implementation spends tens.

For scale: the Merkle walk hashes on the order of 100 MB in a cold
`calc_parser` check ([[sha256-linked-into-cache]], 2026-11-10). At this
speed that alone is longer than the whole run is today. The switch is not
a choice yet.

## Where it goes, read from the code and not yet profiled

1. **A word of the context is read and stored a byte at a time.**
   `s.working.at(i)` and `put` are four `byte_within` reads or stores, each
   under its own compare with the length word, with shifts and ors between.
   A big-endian word is one load and a `bswap`.
2. **Every call saves and restores eight registers.** The bytes of
   `sha256_compress.s` show eight stores to the frame before each `call`
   and eight loads after, whatever is live. The round calls `t1`, `turn`,
   `set`, `shift`, and the word functions under them.
3. **The working variables move in memory each round.** `Sha256::shift` is
   a loop of seven word moves, each a read and a store of the kind in (1).
   An implementation that keeps a to h in registers, or indexes them by the
   round modulo eight, moves nothing.
4. Constants are sixty-four-bit immediates, and a condition is made a word
   and tested again.

## What to do

- A profile first (callgrind's instruction counts by symbol offset, or
  `perf annotate`), so the order of 1 to 3 is measured and not read.
- (1) is a lowering: a word reader over a span for `Stored::u32_be`, one
  compare for the four bytes, then none where the record is held
  (an obligation over the held meaning; not designed in an issue yet).
- (2) is the planner: save what is live across the call
  ([[function-ir-planner-register-pressure]]), and inline a callee called
  once (the `for` thread's note on PR #618).
- (3) is the source: the same specification can be met by a rotating
  index, and `Sha256::run_spec` says what has to stay true.
- ~~A case for bytes a second, beside the scanner's, so the ratio is
  tracked.~~ Done: `scripts/bench-native` (below).

## Done when

The ratio to the cache's scalar path is small enough that
[[sha256-linked-into-cache]] is a decision about trust and not about time,
and the number is tracked.

## Tracked

`scripts/bench-native` (`docs/native/native-benchmarking.md`) prints the table and
records it in `crates/linked/benches/baseline.tsv`: ns per block and MB/s of
the linked code; the same for a Rust mirror of the Heather source
(`crates/linked/benches/native/mirror.rs`, held to the linked code byte for
byte), a textbook scalar Rust and the `sha2` crate, each at opt-level 3 and
0; **instructions per block of the linked compression, counted exactly by
callgrind, with a breakdown by kind** (the optimizer's counter; `--check`
fails when it rises); `compile-x86`'s cold and warm time per SHA-256 export;
and the scanner's MB/s and instructions per byte against the Rust lexer.
A pass that changes emitted code reports the counter's move and re-records.

## Log

- 2026-11-14: The first snapshot (cloud box): linked compression 215,898
  instructions and 3,814 calls a block, frame loads and stores 28% of them;
  about 12,500 ns a block. The mirror at opt-level 3 is about 2,800 ns and
  at opt-level 0 about 33,000, so our compiler already beats rustc without
  optimization on the same source by about 2.7 times, and LLVM's optimizer
  is about 4.4 times better than ours on it. Textbook 250 ns, `sha2` with
  the SHA extensions 40. Compiling a SHA-256 export from an empty store
  takes one to three minutes, and 2 to 12 s over a warm one. Scanner
  37 MB/s and 453 instructions a byte, against the lexer's 101 MB/s and 121.
- 2026-11-14: Cause (2), first half, is fixed: a call saves only the registers whose values are read after it ([[function-ir-verified-live-spills]], closed). The compression went from 216,000 to 175,969 instructions a block and the scanner from 5.11e9 to 3.57e9 over `lib/`, and time moved about 5% on each: the saves were cheap instructions. What the profile's shares do not show is which instructions are on the dependent path; the word accessors (four byte loads, shifts and tests behind a call) and the working variables' moves through memory are. The design the remaining steps follow is `docs/native/optimizer-design.md`.
- 2026-11-14: The profile, after the optimizer's step 4 (`docs/native/optimizer-design.md` §9.1): callgrind's count of every instruction of `sha256_compress`, joined with the disassembly, per block of 133,615 instructions. Words through spans a byte at a time are still most of it, now measured: 7,648 byte loads and 2,608 byte stores (about 2,560 word reads and stores); 15,424 instructions settling a byte that a byte load already zero-extended (`shl 56; shr 56`, often twice in a row); at least 15,264 forming a byte's address (`mov; add` before each access, the model's loads taking `[base]` alone); 5,640 shifts and 4,297 ors joining and splitting the bytes; about 7,000 sixty-four-bit immediates under 128, nearly all the `1`, `2`, `3` added to a byte's index (the model has `ADD r, imm8`; the lowering does not choose it for an addition of a constant). Together about 55,000 to 60,000 of the 133,615, which a word load and store (one access, one `bswap`) leave a tenth of. The rest, in order: register moves not part of an address about 17,000; frame loads and stores 10,534; settling a 32-bit sum or shift 6,464 (`shl 32; shr 32`, a 32-bit move or 32-bit forms halve or remove it, [[x86-narrow-and-rotate-forms]], [[function-ir-narrow-settle-lazily]]); compares and their jumps about 14,000 (the K table's chain and indexes that count in a loop); calls, returns and frames about 4,200. So the order is: the word load (the optimizer's step 5), then a range rule that a narrowing of a value already in range is a move, then `ADD r, imm8` for a constant, then the loop law for the working variables.
- 2026-11-14: Moves and frame traffic of a block by cause (callgrind's per-instruction counts joined with the disassembly, each instruction named by its neighbours; `/mnt/project-files/frames-moves/causes.py`), at 79,955 instructions. Moves, 14,488: a copy before a two-address operation whose source lives on 8,113 (about 2,700 of them `x + K`, an index plus 1, 2 or 3, which `LEA` does in one; about 3,000 inside rotations and settles; 960 `mov; shl 2; add` forming a word's offset); a copy forming an address, `mov r, base; add r, index; [r]`, 3,928, each with its add, so `[base + index]` would take 7,856; an argument moved into place at a call 1,344 (mostly a constant made in one register and moved to the one the call wants); a result into RAX at a return 586; an arm's output at a join 240. Frame, 6,306: caller-saved registers stored round a call and loaded after it 6,048, 3,360 of them in the message schedule's loop; saves at entry 258. Call, return and frame 2,447, of which 1,226 the frame's `add rsp` pair (a leaf frame would take two a leaf call). The kept registers took the frame to 2,230 and the block to 76,685 ([[function-ir-values-in-kept-registers]]); the scanner went from 307.1 to 253.6 instructions a byte.

