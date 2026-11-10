---
title: Link the proved SHA-256 into crates/cache in place of the scalar path
status: open
labels: [cryptography,native,caching,design]
area: heather-in-heather
milestone: [crypto-hash,nh-library]
blocked-by: [native-library-exports-design, sha2-compress-native]
created: 2026-11-10
updated: 2026-11-10
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
