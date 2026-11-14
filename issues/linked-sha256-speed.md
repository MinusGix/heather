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

`scripts/bench-native` (`docs/native-benchmarking.md`) prints the table and
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
