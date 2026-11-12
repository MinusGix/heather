---
title: State that a token's end fits its bits as a premise of the scanner's export
status: open
labels: [native,lexer,exports]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-12
updated: 2026-11-12
---

`token_word_kind` and `token_word_end` (`lib/lang/lexer/lexer_span.hthr`) read a token's word back for an end below `2^TOKEN_END_BITS`. The end `scan_token` returns is at most the span's length (`scan_token_longest`: the specification's offsets are inside the source), and that length is below `2^56` because a lent span ends below `2^47` (`Loan::canonical`, which the export's `SAFETY` comment already cites). Nothing states the chain: Rust's `scanner::token` relies on it in a doc comment ("An end fits its bits").

## What would fix it

A theorem in `lexer_span.hthr` that `scan_token`'s answer, where nonzero, has an end at most `length`, so that with `length < 2^TOKEN_END_BITS` its word reads back by `token_word_kind`/`token_word_end`; and the `length` bound named beside the other premises in the generated declaration of `scan_token` (`heather_cli::linked`), the way `Loan::canonical` is.

## Done when

The read-back of `scan_token`'s own answer is a theorem whose only premise about the length is one the export's `SAFETY` comment discharges.

Split from [[scan-token-word-packing-unproved]] (closed 2026-11-12).
