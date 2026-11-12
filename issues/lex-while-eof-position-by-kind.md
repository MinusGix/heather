---
title: lex_while's closing Eof stands past a refused identifier or numeral and before any other refused token
status: closed
labels: [frontend,lexer,cleanup]
area: language
created: 2026-11-12
updated: 2026-11-12
---

`heather_syntax::lexer::lex_while` stops before the first token its `keep` refuses and ends what it read with `Eof`. Where that `Eof` stands depends on the kind of the refused token (found writing the scanner-run lexer, which has to answer the same, 2026-11-12):

- an identifier, a numeral, a scaled literal, an argument slot or a hole: `Eof` is **past** the refused token, because the loop has advanced its offset before it makes the token;
- any other token: `Eof` is at the refused token's **start**.

The doc comment says "the refused token is the last thing read", which fits both. Nothing is known to read the position (the import pre-scan reads the tokens before it), so this is a wart and not a bug. `lex_into_scanned` copies it on purpose and `the_scanners_run_stops_where_the_lexer_stops` (`crates/linked/tests/scanner.rs`) holds the copy.

To do: one rule (the start, which is where an error's `Eof` already stands), in `lex_into_rust`'s `emit!` and in `lex_into_scanned`, with the test's expectation following. Minor.

## Log

- 2026-11-12: Done: one rule, `Eof` at the refused token's start, in `lex_into_rust`'s `emit!` and `lex_into_scanned`; `the_scanners_run_stops_where_the_lexer_stops` now also checks that position at every stop.
