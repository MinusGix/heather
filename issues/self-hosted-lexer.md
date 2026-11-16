---
title: Heather's lexer as a runtime fn, compiled natively, matching the Rust lexer on lib/
status: open
labels: [native,self-hosting]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-10-31
updated: 2026-11-10
---

Round R7 of `docs/native/compiler-milestones-proposal.md` (§5, §7), milestone `self-lexer`: Heather's lexer, in
Heather, compiled natively. This is the first half of what
[[self-hosting-first-component]] filed.

## Scope

- A pure function from bytes to tokens, written with the sequencing surface, against the token grammar.
- A `runtime fn` under the default setup that streams tokens to stdout, so it needs no heap (Minus, 2026-10-31: lexer before heap, tentatively). The token-list version can follow once [[native-heap-arena]] lands.
- A differential test against `crates/syntax/src/lexer.rs` over every file under `lib/`.

## Done when

`heather-lex` matches the Rust lexer on every file under `lib/`.

## What it assumes from elsewhere

- **[[effects-uniqueness-surface]]** owns the I/O surface, and **[[runtime-fn-default-setup]]** owns the pure fragment.

## Log

- 2026-11-05: gardener: cites a file it shares with [[integer-operator-symbols]] (`crates/syntax/src/lexer.rs`); [[notation-extensibility]] (`crates/syntax/src/lexer.rs`).
- 2026-11-07: readiness assessment (Minus asked whether the stack is ready; probes in the project folder's `self-lexer/`). **Ready:** bytes and text (`BitVec(8)`, `Char`, `String`, UTF-8 encode/decode with the round-trip proved), the pure loop surface (`for`, `let mut`, statement `match`, records, enums), lists and `Nat` for a pure lexer's output and numeral values: a byte-at-a-time state-machine lexer for a token subset checked by `refl` at the first attempt, at about 400 kernel steps per byte. **Partly ready:** running it on real files. A string literal aborts the process at about 2,000 characters ([[long-string-literal-stack-overflow]]), one declaration's fuel covers about 2.5 KB of lexing, and there is no other way to get a file's bytes into a term; the lexer is line-local, so per-line theorems written by a Rust test sidestep all three. Native pure words: `class` (nine-arm byte classifier) and small step functions certify through `compile-x86`, but a caller of a dozen-arm step is refused ([[runtime-fn-caller-agreement-fuel]]) and each small function costs tens of seconds in the generator ([[runtime-generator-link-cost]]). **Blocked:** byte buffers in a `runtime fn` (Get/Set and `Fold` over a buffer, in flight in [[runtime-default-setup-soundness]]) and I/O (rt to `Source` with `sound`, branches and loops over the world, `runtime fn main`: [[effects-uniqueness-surface]]'s remaining slices). The heap is not needed for the streaming version. First slice that can start now: [[heather-lexer-evaluated]], the pure lexer with a per-line differential test against this file's Rust lexer, whose step is the one the native round later compiles.
- 2026-11-07: [[runtime-fn-caller-agreement-fuel]] fixed: `step(st, b) = step_full(st, class(b))` from the readiness probes now checks (its agreement links callees by `calls_fit`). Its `compile-x86` still runs out of fuel in the certificate's `program_evaluable`: [[function-ir-evaluable-quadratic]].
- 2026-11-07: [[long-string-literal-stack-overflow]] closed: a string literal of any length now checks (a 178 KB file's text elaborates as a `String`), so a file's bytes can reach a term as a literal. Two limits remain on that route: one declaration's fuel (a `String::len` by `refl` runs out past about 100,000 characters), and comparing two long lists by value, which meets the conversion's depth budget at about a thousand elements ([[long-vector-conversion-depth]]); a `lex(src) = tokens` theorem over a whole file meets the second.
- 2026-11-07: [[function-ir-evaluable-quadratic]] fixed: `compile-x86` of the probes' `step` certifies (1483 program bytes); the certificate checks evaluability in one pass per function, and the largest, `step_full`'s, takes about 29% of a declaration's fuel. A function about twice its size would run out again: [[function-ir-scan-id-cost]].
- 2026-11-10: Minus (2026-11-10) named the target as "lexer in Heather linked directly".
  `docs/native/native-lexer-crypto-roadmap.md` reads that as the scanner linked into
  the `heather` binary ([[self-lexer-linked]]), which needs no effects surface
  and no heap: the caller owns the source bytes and the token buffer. The
  `heather-lex` process of this issue becomes the side branch: the same
  scanner behind a process wrapper, once `nh-effects` has its surface.
  Whether `self-lexer`'s done-when moves to the linked form is decision 3 of
  that note's §9.
- 2026-11-10: The scanner exists as certified Heather linked into Rust ([[self-lexer-linked]], [[heather-lexer-evaluated]]); `heather-lex` as a process would reuse `lexer_scan.hthr` unchanged, since its step takes one byte and carries everything else in the state word.
