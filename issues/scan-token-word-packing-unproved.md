---
title: The token word's packing is read apart in Rust and held by tests only
status: closed
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

## Log

- 2026-11-12: the read-back and the nonzero word are theorems, and the constant is generated. In `lexer_span.hthr`: `def TOKEN_END_BITS: Nat = 56`, which `token_word` shifts by; `token_word_kind` (`word.shift_right(TOKEN_END_BITS) = kind`) and `token_word_end` (`word.band(ofNat(2^TOKEN_END_BITS - 1)) = end`), for `kind < 256` and `end < 2^TOKEN_END_BITS`; `token_word_nonzero` (`kind ≠ 0` gives `word ≠ 0`). The proofs are the bits moved, not `bv_decide` (there is none): kind and end are their low bits zero-extended (`BitVec::zero_extend_take_low_of_lt`, new in `bitvec.hthr`), and the halves are joined end-first (`bor_comm`, `band_comm`) so each reading keeps `False || bit` and `True && bit`, which compute; a neutral `bit || False` does not. The constant: `crates/linked/generated/CONSTANTS.tsv` names `lexer_span.hthr`'s `TOKEN_END_BITS`, `scripts/linked` (`heather linked-exports`, `heather_cli::linked::constants_rs`) writes `generated/constants.rs` from the `def`, which must be a numeral, and `crates/cli/tests/linked_exports.rs` holds the file to the module; `scanner::token` and the spans test read it from there. The third claim, that an end fits, is a premise of the export and moves to [[scan-token-end-fits-premise]]; the write half that would retire the packing stays [[native-library-exports-design]]'s R4.
