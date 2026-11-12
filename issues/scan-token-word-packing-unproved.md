---
title: The token word's packing is read apart in Rust and held by tests only
status: open
labels: [native,lexer,exports]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-12
updated: 2026-11-12
---

`scan_token` (`lib/lang/lexer/lexer_span.hthr`) answers one word: the token's kind above bit 56 and the offset past it below, zero for a refusal (`token_word`). `scan_token_longest` says that word is `Accepted::word` of the specification's scan. What reads the word apart is Rust, `scanner::token` in `crates/linked/src/scanner.rs`: a shift and a mask, with `END_BITS = 56` written a second time there.

So three things are held by tests only (`crates/linked/tests/scanner.rs`), and each is a statement Heather can make:

- `token_word(kind, end)` read back: `word.shift_right(56) = kind` and `word.band(mask) = end` when `kind < 256` and `end < 2^56`.
- A token's word is never zero (every kind the automaton accepts is nonzero, [[self-lexer-linked]]'s kinds table), so zero means only a refusal.
- An offset fits: `end <= length`, and a span's length is below `2^56` on every machine the code runs on. This one is a premise of the export, to be stated beside the others in the generated declaration.

## What would fix it

The first two as theorems in `lexer_span.hthr` by `bv_decide` or by the shift laws. Then either the Rust reads the word through two more linked functions (`token_kind`, `token_end`; two more calls a token, so probably not), or the constant is generated: `scripts/linked` writes `END_BITS` into `generated/exports.rs` from the module, and the test compares.

The better end is the write half of the export ([[native-library-exports-design]] round R4): `scan_token` writes the kind and the end into a two-word span its caller lends, and there is no packing.

## Done when

No constant of the packing is written by hand in Rust, and the read-back is a theorem or the packing is gone.
