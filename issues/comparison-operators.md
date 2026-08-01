---
title: Surface <= (and <): one lexer token and one infix-table row each
status: open
labels: [frontend,syntax,ergonomics]
created: 2026-08-01
updated: 2026-08-01
---

The infix machinery from [[surface-operators]] is a desugar table: `infix_op` (crates/syntax/src/parser.rs:912) maps a token to a global name and binding powers, and the parser emits an ordinary `ExprKind::Call` — `Plus => ("add", 3, 4)`. Adding an ordering comparison is therefore one lexer token plus one table row, NOT a reopening of [[surface-operators]] and NOT the open-ended [[notation-extensibility]] question.

Design points to settle (small, but real):

- **Desugar target.** `n <= m` should desugar to `Le(n, m)` — the named proposition from [[le-named-proposition]], which this issue wants landed first — so that `theorem fuel_monotone(…, hle: n <= m)` is writable and means the Type, not a Bool. If a boolean is wanted in computational position, `leb` stays callable by name; do not make `<=` context-sensitive.
- **Binding power** relative to `==` and `+`: comparisons bind looser than arithmetic, and `a <= b == c` should probably be a parse error (non-associative at its own level) rather than either association silently.
- **`<`** comes along as `Lt(n, m)` (definable as `Le(Succ(n), m)`) if the kit wants it; don't add `>=`/`>` flipped forms until a use site asks — argument-order flips are exactly what [[method-receiver-position]] taught to be suspicious of.
- **Lexer care:** `<=` must not collide with the generics lexing of `<` (`Monoid<A>`); the tyargs path and the expression path need the usual disambiguation check.

Acceptance: `fuel_monotone` and the le-kit stated with `<=`; a parse-error negative control for `a <= b <= c`; a generics declaration still parsing in the same file.
