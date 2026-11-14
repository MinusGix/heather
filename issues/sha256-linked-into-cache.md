---
title: Link the proved SHA-256 into crates/cache in place of the scalar path
status: open
labels: [cryptography,native,caching,design]
area: heather-in-heather
milestone: [crypto-hash,nh-library]
blocked-by: [native-library-exports-design, sha2-compress-native]
created: 2026-11-10
updated: 2026-11-14
---

Stage C2 of `docs/native-lexer-crypto-roadmap.md` §4: the compiled, proved
SHA-256 linked into `crates/cache` in place of the scalar path of
`crates/cache/src/sha256.rs`.

That file's header says why this is the first cryptography target: a cache
entry is believed at rung 1, so a collision is a wrongly accepted proof,
"which puts this module in the same category as the kernel". A proved
implementation leaves only the cryptographic assumption there.

## Scope

- `compress` exported under [[native-library-exports-design]]'s contract:
  reads the 64-byte block, writes the eight-word state, nothing else.
- The streaming wrapper (`update`, `finish`, the 64-byte carry buffer)
  either stays in Rust around the exported `compress`, or moves across
  with [[sha2-specification]]'s streaming theorem. Start with Rust around
  `compress`: it is the smallest trusted wrapper.
- The file is also compiled into `build.rs` by path. The build script
  keeps the Rust scalar path (it fingerprints the kernel source before
  anything is built); say so in the header.
- A switch (a Cargo feature or an environment variable), off by default
  until Minus turns it on: it changes the trust base.
- The SHA-NI path stays as it is until stage C7.

## Done when

With the switch on, every cache key over the suite is unchanged, the NIST
vectors of `crates/cache/tests/sha256.rs` pass on the linked code, and the
regeneration gate holds the checked-in artifact to its source.

## What it assumes from elsewhere

- **[[sha2-compress-native]]** owns the function and its theorem.
- **[[native-library-exports-design]]** owns the contract, the artifact and
  the gate.

## Log

- 2026-11-10: One of the two blockers moved: SHA-256's word functions are compiled, proved and linked ([[sha2-compress-native]]), and `heather_linked::sha256::digest` matches the `sha2` crate, the oracle `crates/cache/tests/sha256.rs` holds the compiler's hash to, on every test. It is not a candidate to switch on yet. The linked `compress` is Rust around three calls per round, so the proof covers the arithmetic and not the state handling, and it is slower than the scalar path by the call overhead. This issue waits, as written, on `compress` exported whole.
- 2026-11-10: A datum for the size of the prize, from a kernel-performance round's
  whole-run profile (callgrind, cold `docs/showcase/calc_parser.hthr` with a
  cache directory, cloud box, width one): `Sha256::compress_blocks` is
  4,455 M of the run's 51,332 M instructions (8.7%), the largest single
  function. Nearly all of it is the Merkle walk's (`merkle::Walk::node`:
  1.7 M term and 0.74 M type visits over 254,000 walks, about 110 MB hashed),
  0.5 G is `module_image::projected_interface`. In seconds it is much less
  than its instruction share, since the code is straight-line: the
  `merkle_walk_ns` column is 0.22 s of a 15 s run.
- 2026-11-12: What this issue waits on has changed shape (2026-11-12, [[sha2-compress-native]]'s log). There is a linked SHA-256 with `crates/cache`'s three calls, `heather_linked::sha256::stream::Sha256` (`new`, `update`, `finish`), every byte of it compiled Heather with its certificate, the padding included, so the "smallest trusted wrapper" in Rust is now 328 bytes lent and three calls. It is **not proved against the specification**: the certificates say the code computes the Heather functions, and that those are SHA-256 rests on tests (the NIST vectors, the `sha2` crate at every length and every split). So the title's "proved" is not met, and switching the cache to it today would put tested-but-unproved code under every cache key in place of tested Rust. Nothing here was switched; the switch, with or without the proof first, is Minus's. Also to weigh before it: the linked code takes a byte at a time and keeps its working variables in memory, so it is much slower than the scalar Rust path, unmeasured ([[linked-scanner-speed-unmeasured]] is the same question for the scanner).
- 2026-11-14: The linked hash is now proved against the specification: `Sha256::digest_spec` (`lib/native/crypto/sha256_stream_agreement.hthr`) says the digest a context holds after `init`, `update` and `finish` is `Sha2::digest` of the message, for any number of parts (`Sha256::update_took`, `Sha256::finish_digest`), over `Sha256::run_spec` for the compression. With the generator's `*_holds` theorems it reaches the record the span holds after the linked code. One seam is left before the bytes the Rust wrapper copies out: [[stored-record-bytes-from-held-value]]. The switch is still Minus's, and the speed question is unchanged. A tactic gap met on the way: [[bv-omega-hypothesis-word-bound]].
- 2026-11-14: The seam is closed: `Sha256::linked_digest` states the agreement on the span, that the thirty-two bytes at `SHA256_DIGEST_AT` after the code of `init`, `update` and `finish` are `Sha2::digest(message)` ([[stored-record-bytes-from-held-value]]). What the Rust wrapper adds is lending the spans and copying those bytes out.
- 2026-11-14: Speed measured for the first time: [[linked-sha256-speed]]. About 6.5 MB/s against about 1,400 MB/s for a hash using the CPU's SHA instructions, nine tenths of it in the compression. Not switchable at this speed; the issue names what to fix.
- 2026-11-14: The small language gaps the proof met are listed in [[surface-gaps-from-sha256-proof]].
