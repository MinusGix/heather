---
title: The linked scanner answers its refusals and fills the token list itself
status: open
labels: [self-hosting,lexer,native]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-14
updated: 2026-11-14
---

Two outputs the Rust side of the linked scanner still computed by lexing
again or by driving the loop (side-thread brief §8 of
`/mnt/project-files/design/optimizer-side-threads-2026-11-14.md`, for the
optimizer thread; part of [[self-lexer-linked]]):

1. **The refusal.** `scan_token` answered zero for every refusal, and
   `heather_syntax::lexer::lex_scanned` lexed the whole file again with the
   Rust lexer for the message. Wanted: the reason and the offset from the
   linked scanner, mapped to the Rust lexer's message, so a refused file is
   lexed once.
2. **The token list.** Rust calls `scan_token` once per token. Wanted: a
   linked function that fills a caller-lent span with (kind, start, end)
   records and returns the count (count-then-fill, or fill-until-full with a
   resume offset), proved against the evaluated specification the way
   `scan_token_longest` is.

Token values (numerals, strings with escapes) wait on #611 and are not in
scope. `HEATHER_LEXER=linked` stays off by default (Minus, 2026-11-14).

## Design of the refusal

- A state that refuses is `FAIL` in its low byte and the reason above it,
  where an accepting state has its kind (`lexer_scan.hthr`, `FAIL_*` and
  `REFUSED_*`). The automaton names the reason on the edge that refuses, so
  there is no second table of reasons to keep in step with it.
- The answer word of `scan_token` is `refusal_word(reason, at)`: zero in the
  top byte (no kind is zero), the reason in the byte below, the offset in the
  low 48 bits. `refusal_word_parts` reads it back. Before anything is
  accepted the loop's answer is `REFUSED_UNEXPECTED` at the token's start,
  so "stopped having accepted nothing" needs no case of its own.
- The specification answers `Cut::Found` or `Cut::Refusal(reason, at)`, and
  `Scanned::Refused(start, reason, at)`; `scan_token_longest` covers both.
- Rust: `ScanRefusal` (`crates/syntax/src/lexer.rs`) numbers the reasons as
  the module does, and `ScanRefusal::error(src, start, at)` builds the
  message from the same builders the Rust lexer now calls, so the two cannot
  drift in wording. Where the message needs a position other than the one
  refused, the reason says which (`Mark`: the byte before; `SignedMark`: two
  before), or the automaton runs on to where the Rust lexer's span ends:
  a width suffix's leading zeros run to the end of its digits
  (`SUF_ZEROS`), and a character literal of more than one scalar value runs
  to its closing quote (`step_char_more`), so the message can say how many
  it holds. Two positions a finite automaton cannot carry to its refusal
  are found by the message builder in the token's own bytes: the suffix
  letter of `LeadingZeros`, and the misplaced `_` of `FractionUnderscore`,
  which only the exponent after it shows to be an error.
- What is read in Rust is values only: an earlier escape's or an exponent's
  value can be refused before the shape that follows it, as the Rust lexer
  does, so the builder reads those first.

## Design of the token loop

- `lexer_records.hthr`: `out.scan_tokens(olen, source, length, at,
  previous)` stores a record of sixteen bytes for each kept token (start,
  then the token's word, big-endian), then one for the end of the file or
  the refusal, and answers how many. Where the span has no room for the
  next record it stops; the caller goes on from the end of the last record,
  after a token of its kind (`heather_linked::scanner::tokens_by_records`).
  It is fill-until-full with the resume point in the records themselves, so
  there is no count pass and no resume word.
- The specification is `Record::from` (`lexer_tokens.hthr`): `Scanned::from`
  with the tokens before a refusal kept. `scan_tokens_records` proves the
  loop stores `List::put_records` of it, for a source below `2^48`; the
  invariant behind it is `Accepted::longest_inside` (every cut the scan
  answers is inside the source, with a kind or reason of one byte, which
  `scan_accept` now masks to).
- The loop is lent two spans, so the scanner it calls is too: a callee
  reads its caller's spans in their own places, and `scan_token` is lent
  only the source. `scan_token_over` is `scan_token` lent `out` first and
  not reading it (`scan_token_over_is`). With the byte read written into
  its loop rather than called, it compiles; as a call of six words the
  planner refused its placement.
- Fuel bounds the loop as it bounds `Scanned::from`; the next token's
  word is an argument, so it is computed once.

## Log

- 2026-11-14: Refusals built (first PR, #629). The token loop is the second.
- 2026-11-14: Token loop built: `lexer_records.hthr`, exported as
  `scan_tokens`; `tests/scanner.rs` holds `tokens_by_records` to the
  scanner on every source of the repository at one, two, three and 4096
  records a call.
