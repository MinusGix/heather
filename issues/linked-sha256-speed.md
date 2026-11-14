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
- A case in `perf/bench/cases.tsv` or `scripts/bench` for bytes a second,
  beside the scanner's ([[linked-scanner-speed-unmeasured]]), so the ratio
  is tracked.

## Done when

The ratio to the cache's scalar path is small enough that
[[sha256-linked-into-cache]] is a decision about trust and not about time,
and the number is tracked.

## Log

- 2026-11-14: Cause (2), first half, is fixed: a call saves only the registers whose values are read after it ([[function-ir-verified-live-spills]], closed). The compression went from 216,000 to 175,969 instructions a block and the scanner from 5.11e9 to 3.57e9 over `lib/`, and time moved about 5% on each: the saves were cheap instructions. What the profile's shares do not show is which instructions are on the dependent path; the word accessors (four byte loads, shifts and tests behind a call) and the working variables' moves through memory are. The design the remaining steps follow is `docs/optimizer-design.md`.
