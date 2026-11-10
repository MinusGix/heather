---
title: The lexical grammar as data: one table for the Rust lexer, tree-sitter and the Heather lexer
status: open
labels: [self-hosting,lexer,syntax,design]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-10
updated: 2026-11-10
---

Stage L5 of `docs/native-lexer-crypto-roadmap.md` §3. A new lexer symbol
changes three places today: `crates/syntax/src/lexer.rs`, the tree-sitter
grammar (whose check is not in CI), and, once it exists, the Heather lexer.
The token grammar should be one piece of data that all three read.

## Scope

- Heather's token classes as `regex def`s (`lib/std/text/regex.hthr`), with
  a priority order, and a `lexer def` generator that publishes the scanner
  as the meaning "longest match, first class on a tie".
- The DFA from [[regex-dfa-compiler]] as its compiled form: a table
  ([[rt-fixed-arrays-and-tables]]) and a table-driven step, with the
  theorem that the generated scanner is [[heather-lexer-evaluated]]'s.
- The tree-sitter symbol inventory generated from the same data.

## Done when

Adding a punctuation token is one line of the grammar data, after which the
Heather scanner, its compiled table and the tree-sitter inventory all
change, and the hand-written step is deleted.

## What it assumes from elsewhere

- **[[regex-dfa-compiler]]** owns the DFA and `dfa_sound`. This issue is its
  first customer with more than one regex.

## Log

- 2026-11-10: There is now an automaton to generate: `lib/lang/lexer/lexer_scan.hthr` was written from a transition table (a Python model held to the Rust lexer before any Heather was written), and its states, kinds and families are the data this issue would own. Two facts the generated form must keep, found by the differential tests: a scanner needs a refusal no earlier accept excuses (`FAIL`: `12abc`, an unterminated literal) beside the ordinary dead end, and one token's start state depends on the previous kind (`>>`).
