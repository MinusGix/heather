---
title: A differential harness for compiled exports against their Rust references
status: open
labels: [native,testing,tooling]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-10
---

Both targets of `docs/native-lexer-crypto-roadmap.md` replace a Rust
component by compiled Heather, and both need the same test: run the export
against the Rust reference on a corpus and on random inputs.
`examples/x86-native/main.c` does this by hand for one function.

## Scope

- One harness (a Rust test binary, since the references are Rust): given an
  exported symbol, its Rust reference and an input generator, link the
  certified assembly and compare outputs; report the first differing input.
- Corpus mode (every file under `lib/` for the lexer) and random mode
  (seeded, reported by seed, as the kernel's property tests are).
- The regeneration gate [[native-library-exports-design]] asks for: rebuild
  the checked-in artifact and compare bytes.
- Under `scripts/test`'s rails, placed with the native gates so `--pr`
  runs it only when its inputs change.

## Done when

The scanner against `heather_syntax::lex` and `compress` against
`crates/cache/src/sha256.rs` run through it, and a deliberately wrong
artifact is reported with the input that shows it.

## What it assumes from elsewhere

- **[[self-lexer-linked]]** and **[[sha256-linked-into-cache]]** are its
  first two users.
