---
title: "Carrier-directed infix subtraction notation"
status: open
labels: [frontend,syntax,notation,stdlib,ergonomics]
created: 2026-08-20
updated: 2026-08-20
---

`Nat` and `Int` both expose `sub`, but their laws still read
`sub(m, 0) = m` and `sub(n, n) = 0`. Add carrier-directed binary `-` so those
statements can use the mathematical surface `m - 0 = m` and `n - n = 0`.

This is distinct from prefix negation: the designation key already separates
fixity and arity, as required by [[prefix-negation-notation]]. `Nat` installs
truncated subtraction; `Int` installs additive-group subtraction. The parser
should give infix `-` the same precedence and associativity family as `+`, while
continuing to recognize prefix `-` and `->` unambiguously.

## Acceptance

- Both `Nat` and `Int` can designate their own binary `-` without collision.
- Standard-library subtraction laws use infix notation in public statements.
- `a - b - c`, `a + b - c`, `-a - b`, and `->` have pinned parses.
- Imported carriers remain unambiguous once operands or expected type identify
  the carrier.

## Log

- 2026-08-20: Filed from the standard-library surface review. Prefix
  negation deliberately reserved this separate fixity slot but did not add it.
