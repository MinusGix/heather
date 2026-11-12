---
title: Heather's scanner compiled natively and linked into the heather binary
status: open
labels: [self-hosting,lexer,native]
area: heather-in-heather
milestone: [self-lexer,nh-library]
blocked-by: [heather-lexer-evaluated, native-library-exports-design]
created: 2026-11-10
updated: 2026-11-12
---

Stage L3 of `docs/native-lexer-crypto-roadmap.md` §3: Heather's scanner,
compiled natively, linked into the `heather` binary in place of the
tokenizing loop of `crates/syntax/src/lexer.rs` (Minus, 2026-11-10: "lexer
in Heather linked directly"). [[self-hosted-lexer]] is the other front end
on the same scanner, a `heather-lex` process, and waits on `runtime fn
main`; this one needs no effects and no heap.

## Scope

- `next_token(src, len, pos)` returning (kind, end), a `runtime fn` over a
  read-only borrowed span, iterating [[heather-lexer-evaluated]]'s step.
  Kinds and spans only: a token's value (a numeral past a machine word, an
  unescaped string) is computed from its span on the Rust side at first.
- Exported under [[native-library-exports-design]]'s contract and linked
  behind a switch. `heather_syntax::lex` becomes a loop over it that builds
  `Vec<Tok>`.
- Errors: the scanner returns an error kind and an offset; Rust re-lexes
  the file with its own lexer for the message, so diagnostics do not
  change.
- Bootstrap: the Rust lexer stays as stage 0, as the fallback on hosts that
  are not x86-64 Linux, and as the oracle.
- A differential gate over every file under `lib/` and over random byte
  strings ([[native-differential-harness]]); `scripts/perf ab` for the
  front end's time with the switch on.

## Done when

With the switch on, the token stream equals the Rust lexer's on every file
under `lib/`, the suite is green, and the regeneration gate holds the
checked-in artifact to `lib/lang/lexer.hthr`.

## What it assumes from elsewhere

- **[[heather-lexer-evaluated]]** owns `lex` and its step. Assumed here:
  that it is a scanner (kind and span) with values computed apart.
- **[[runtime-default-setup-soundness]]** owns byte reads in the pure
  fragment; **[[function-ir-multi-word-calls]]** two result words.
- **[[function-ir-scan-id-cost]]**: the full step is several times the
  largest function certified so far.
- **[[lexical-grammar-as-data]]** owns the table the scanner, the Rust lexer
  and tree-sitter would share; this issue does not wait for it.

## Log

- 2026-11-10: Stage L1 and the comparison of L3 are built, with the loop on the Rust side. `crates/linked` links the automaton's twenty-six certified functions (twenty-three families of states, `scan_family`, `scan_accept`, `scan_begin`) and `crates/linked/src/scanner.rs` runs the longest-match loop over them: `Scanner`, an iterator of kinds and spans. `tests/scanner.rs` holds it to `heather_syntax::lex` on every Heather source in the repository and three generated corpora. Three things are still Rust and are this issue's remaining scope, each waiting on a named piece: (1) the pick of a family in `step`, until one program can hold them all ([[runtime-generator-program-size]]); (2) the loop itself, until a compiled function can read a borrowed span ([[native-library-exports-design]]), at which point it is `lexer_tokens.hthr`'s `Accepted::longest` compiled; (3) the switch in `heather_syntax::lex`, which needs the values computed from spans and wants (2) first so the switch is not a per-byte call across the boundary. The done-when's module path is `lib/lang/lexer/`, not `lib/lang/lexer.hthr`.
- 2026-11-10: The automaton is one program now. `scan_step` is a `runtime fn` (`scan_family`, then `scan_choose` over the twenty-three families), certified as one program of twenty-six functions and linked as one export; `scanner::step` is one call and the table of families Rust held is gone. `crates/linked/generated` holds `scan_step.s`, `scan_accept.s` and `scan_begin.s`. The limits that had kept it apart are closed ([[runtime-generator-program-size]], [[compile-x86-certificate-memory]]); what bounds a single family is [[native-function-emission-one-statement]]. Still open here, unchanged: the loop compiled over a borrowed span (L2), the values, and the switch (L3).
- 2026-11-10: The limit on a single function moved: a tree of a hundred comparisons certifies as one function ([[native-function-emission-one-statement]], closed), so no family of the automaton is near it. What the scanner still wants from the compiler is the borrowed read ([[native-library-exports-design]]).
- 2026-11-11: Round E's first parts are built (PR #551): a function that reads a span its Rust caller owns is exported with a generated declaration. The scanner's own loop is written as a `runtime fn` (`scan_token` over the source span, an offset and the previous kind) and does not get its instance yet: the generator runs out of the conversion budget on a measured loop that carries the automaton's state, [[runtime-measured-instance-conversion-budget]]. That is what stands between this and one linked call per token.
- 2026-11-12: The loop is Heather's and linked (L2). `lib/lang/lexer/lexer_span.hthr`: `scan_token(source, length, at, previous)` is a `runtime fn` over the source span, compiled with the automaton under it as one certified program and exported (`scan_token.s`); `scan_token_longest` proves it is `Accepted::longest` at the suffix, the call `Scanned::from` makes. `scanner::token` is one call per token and `Scanner` keeps only the iteration (dropping whitespace and comments, making values). `tests/scanner.rs` holds it to `heather_syntax::lex` on every source as before, and to the Rust loop it replaced from every offset of the lexer's sources; `tests/spans.rs` has its guard-page and stack-alignment controls. Three things were in the way and are written up where they belong: [[runtime-measured-instance-conversion-budget]] (the generator's proof, fixed), the certificate's quiet check (now a function at a time), and [[function-ir-planner-register-pressure]] (worked round in the source, open). Remaining here: the values computed from spans, and the switch in `heather_syntax::lex` (L3); the word's packing (`token_word`) read back by a theorem rather than by Rust's shift and mask.
- 2026-11-12: Filed beside this from the same round, as the smaller things the loop met: [[scan-token-word-packing-unproved]], [[linked-exports-share-one-program]], [[linked-scanner-speed-unmeasured]], [[runtime-loop-over-several-spans]], [[native-certificate-whole-program-evaluations]], and in the language [[numeral-arm-fixes-nat-before-the-other-arm]], [[annotated-let-relation-needs-parentheses]], [[omega-certificate-drops-type-arguments]]. Next here is the register planner ([[function-ir-planner-register-pressure]]).
- 2026-11-12: The switch is built, off by default. `heather_syntax::lexer` takes a scanner as a function (`Scan`: source, offset, previous kind's code, to a kind's code and an end), for one call (`lex_scanned`, `lex_while_scanned`) or installed for the process (`install_scanner`); the crate has no dependency on `crates/linked` and compiles the same with and without one. The `heather` binary depends on `heather-linked` on x86-64 Linux and installs `scanner::token` when `HEATHER_LEXER=linked`; `HEATHER_LEXER_REPORT` prints, as the process ends, how many sources the scanner cut and how many were left to the Rust lexer.

  With a scanner, the scanner decides where each token starts and ends and which kind it is. A token's value is read by the Rust lexer from the token's span alone, and must come back as one whole token of the scanner's kind (`>` and `>>`, which a span alone cannot tell apart, take the scanner's kind). Where the scanner refuses, or a span does not read so, the whole source is lexed again by the Rust lexer, so every message is the one it gives. A cargo feature was the other shape considered and not taken: it compiles `heather-syntax` and everything above it twice.

  Held by: `crates/linked/tests/scanner.rs`'s last section (the run equals `lex_rust` token for token, values included, on every Heather source in the repository, on generated strings and on lines with a character changed, and refuses with the same message and place; `lex_while` stopped at every token of a line; the third copy of the kind numbering, `scan_code`, against `Kind`; six scanners that are wrong, each left unheard, and one that is wrong in the way the lexer cannot see, as a test of where the trust is) and `crates/cli/tests/check.rs` (`heather check` with the switch on prints what it prints with it off, for a good file, a bad one, an import closure and a source that does not lex).

  What is left before the default can move: the speed ([[linked-scanner-speed-unmeasured]]; with the switch every token is also read once by the Rust lexer for its value, so the switch costs more than the scan alone), the values in Heather ([[heather-lexer-evaluated]]), and the refusal's message from Heather. The done-when here asks for the token stream on every file under `lib/` and a green suite with the switch on: the first holds by the tests above; the second is a suite run under `HEATHER_LEXER=linked`, recorded below when it has been made.
- 2026-11-12: Filed from the switch: [[lex-while-eof-position-by-kind]].
- 2026-11-12: The binary now links what it generates, which a merge conflict in `generated/` turns into a build that cannot repair itself: [[linked-assembly-bootstrap]] has the recovery (restore a complete file, build, `scripts/linked`).
