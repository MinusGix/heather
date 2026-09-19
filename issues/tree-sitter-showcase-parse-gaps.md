---
title: Two checked showcase files do not parse: a char literal in parentheses, and a calc chain over ≈
status: open
labels: [tooling,editor,syntax]
created: 2026-09-19
updated: 2026-09-19
---

Two showcase files that the compiler accepts do not parse under the Tree-sitter
grammar, so an editor shows the project's flagship character grammar as one
long error. Both were invisible because `scripts/check-tree-sitter` parses the
whole of `lib/` and `crates/` but exactly one file from `docs/showcase/` —
`calc.hthr`. Extending it to the showcase manifest ([[showcase-harness]]) is
what found them.

**1. A character literal inside parentheses.** `docs/showcase/calc_text.hthr`
row 135 (`Sum(l, tr, r) => spell(l, Cons('+', tr ++ spell(r, tail)))`), and it
reduces to:

```heather
fn f() -> X { 'a' }        // parses
fn f() -> X { ('a') }      // ERROR
fn f() -> X { g('a') }     // ERROR
```

So the literal is in the grammar but not in whatever expression position a
parenthesis or an argument list opens. Every character literal in the
scannerless calculator is an argument to `Cons`, so the whole file is red.

**2. A `calc` chain over a relation other than `=`.**
`docs/showcase/finite_set_client.hthr` row 14, and it reduces to:

```heather
theorem t(): X { calc { a = b := p, = c := q, } }    // parses
theorem t(): X { calc { a ≈ b := p, ≈ c := q, } }    // ERROR
```

The language accepts the `≈` chain — the file checks — so this is the grammar
lagging [[calc-equational-chains]]'s landed surface, not a question about which
relations `calc` should admit (that is [[calc-over-order-relations]], and it is
about the elaborator).

Reproduce from `tree-sitter-heather` after `tree-sitter generate`:

```text
XDG_CACHE_HOME=/tmp/heather-tree-sitter-cache node_modules/.bin/tree-sitter \
  parse ../docs/showcase/calc_text.hthr ../docs/showcase/finite_set_client.hthr --quiet
```

Verified 2026-09-19 against a parser generated from this tree's `grammar.js`
in a scratch copy, so neither is a stale committed `src/parser.c`.

The two idealized files (`idealized.hthr`, `finite-sets-idealized.hthr`) also
fail to parse and are **not** part of this: they are written in syntax that
does not exist yet, which is their job.

## What it assumes from elsewhere

- **[[showcase-harness]]** owns the manifest and the parse set derived from it.
  Assumed here: only that the showcase files it marks checkable are files the
  compiler accepts, so a parse failure on one is a grammar defect.

## Log

- 2026-09-19: Filed from the harness round. `scripts/check-tree-sitter` parses
  the manifest's checkable rows as of that round, with these two files listed
  as known-failing in the script so the check stays green and the exclusion
  list is the thing that shrinks when this issue is fixed.
