---
title: "designation < at T cannot be parsed: the tyvar list opens with the same token"
status: open
labels: [frontend,syntax]
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]). Smallest item that round found,
and it is one token.

The grammar is `desig := "designation" tyvars? OP "at" type ":=" expr`
(`crates/syntax/src/parser.rs`), and `tyvars` opens with `<`. So

```heather
designation < at Int := Lt
```

parses `<` as the start of a type-parameter list and dies at
`expected `>` to close the type parameters, found Ident("Int")`. `<=` is a
distinct token and is unaffected: `designation <= at Int := Le` works, and
`lib/std/int.hthr` has it.

The parser's own message for a bad symbol lists `<` as designable
("the symbols are `+`, `++`, `*`, `&&`, `||`, `<=` and `<`"), so this is a
grammar/documentation disagreement rather than a decision.

## Consequence, which is small but real

`<` at a second carrier falls back to the ambient name `Lt`
(`Elaborator::op_fallback`), and in a file importing both `nat` and `int` that name
is ambiguous — so `a < b` at integers is unwritable there and the round's test
probes spell `int::Lt(a, b)`. Every *other* operator the file wanted is reachable.

## The fix

One lookahead: `<` followed by `at` is the operator, not a type-parameter list.
The same speculative-parse trick [[comparison-inside-type-arguments]]'s round used
for `ident <` in type position, one rung down and much simpler — the follow set
here is a single keyword.

## What it assumes from elsewhere

- **[[comparison-operators]]** owns `<`/`<=` as surface tokens. Assumed here: only
  that `<` is a token the designation table is meant to accept, which that issue's
  log and the parser's error text both say.

## Log

- 2026-08-17: Filed by the `Int` round; ranked last of six. `lib/std/int.hthr` carries a comment where the row would be.
