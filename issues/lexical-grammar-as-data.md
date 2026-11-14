---
title: The lexical grammar as data: one table for the Rust lexer, tree-sitter and the Heather lexer
status: open
labels: [self-hosting,lexer,syntax,design]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-10
updated: 2026-11-14
---

Stage L5 of `docs/native-lexer-crypto-roadmap.md` §3. A new lexer symbol
changes three places today: `crates/syntax/src/lexer.rs`, the tree-sitter
grammar (whose check is not in CI), and, once it exists, the Heather lexer.
The token grammar should be one piece of data that all three read.

## Scope

- Heather's token classes as `regex def`s (`lib/std/text/regex/regex.hthr`), with
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
- 2026-11-14: The kinds are one table. `TOKEN_KINDS` (`lib/lang/lexer/lexer_kinds.hthr`) is a row per kind: its `KIND_*`, its `TokKind` name and its spellings. `scripts/linked` writes `crates/linked/generated/kinds.rs` from it (`heather_cli::linked::kinds_rs`, refusing a `KIND_*` with no row, a misnamed or misplaced row and a spelling of two kinds), and that one file is both `heather_linked::scanner::Kind` and `heather_syntax::lexer::ScanKind`, so `scan_code` names kinds and numbers none. The module proves by evaluation that the codes are the positions and each spelling is one whole token of its kind to the scanner (in three parts: the whole is past one conversion's fuel); `crates/linked/tests/scanner.rs` tests the same of the Rust lexer and the compiled scanner; `scripts/check-tree-sitter-inventory.js` holds the inventory's fixed symbols to the spellings. What is left of the done-when: the spellings are data, but the automaton's states and the Rust lexer's matching are still written by hand, so a new punctuation token is still a `KIND_*`, its states, a row, a `scan_kind` arm and an inventory line (each refused if missing), not one line. Generating the states is the DFA part of this issue ([[regex-dfa-compiler]]).
