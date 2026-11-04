---
title: Heather's lexer as a runtime fn, compiled natively, matching the Rust lexer on lib/
status: open
labels: [native,self-hosting]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-10-31
updated: 2026-10-31
---

Round R7 of `docs/compiler-milestones-proposal.md` (§5, §7), milestone `self-lexer`: Heather's lexer, in
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
