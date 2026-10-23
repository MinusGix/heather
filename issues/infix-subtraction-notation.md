---
title: "Carrier-directed infix subtraction notation"
status: open
labels: [frontend,syntax,notation,stdlib,ergonomics]
area: language
created: 2026-08-20
updated: 2026-10-14
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
- 2026-09-16: Landing this makes `-` the second token whose role its kind does not determine (`a - b` vs prefix `-b`), which [[heather-formatter]] must disambiguate from the AST exactly as it does `<`. No constraint on this issue; its role table is being built general so this costs nothing when it lands.
- 2026-10-12: The `designation - at Int` / `at Nat` half is in the library, but the formatter still writes every `-` as a tight prefix, so binary subtraction is checked in as `a -b` (`lib/std/num/int.hthr`, and `lib/std/tactic/ring.hthr` from the ring round, which `repository_sources_are_formatted` rejected spelt `a - b`). The 2026-09-16 entry's AST disambiguation is the fix; one reformat of `lib/` follows it.
- 2026-10-14: `Rat` now designates binary `-` too ([[rational-order-completion]]), and its distance laws (`abs_sub_comm`, `dist_triangle`, the showcase's `two_halves_close`) are checked in as `(x -y).abs()`.
- 2026-10-21: The formatter still treats `-` as prefix-only and writes infix subtraction tight; [[fmt-infix-minus-tight]].
- 2026-10-21: [[fmt-infix-minus-tight]] closed: the formatter spaces binary `-` from the parse and the library is reformatted, so subtraction reads `a - b` again.
