---
title: Surface <= (and <): one lexer token and one infix-table row each
status: closed
labels: [frontend,syntax,ergonomics]
created: 2026-08-01
updated: 2026-08-16
---

The infix machinery from [[surface-operators]] is a desugar table: `infix_op` (crates/syntax/src/parser.rs:912) maps a token to a global name and binding powers, and the parser emits an ordinary `ExprKind::Call` — `Plus => ("add", 3, 4)`. Adding an ordering comparison is therefore one lexer token plus one table row, NOT a reopening of [[surface-operators]] and NOT the open-ended [[notation-extensibility]] question.

Design points to settle (small, but real):

- **Desugar target.** `n <= m` should desugar to `Le(n, m)` — the named proposition from [[le-named-proposition]], which this issue wants landed first — so that `theorem fuel_monotone(…, hle: n <= m)` is writable and means the Type, not a Bool. If a boolean is wanted in computational position, `leb` stays callable by name; do not make `<=` context-sensitive.
- **Binding power** relative to `==` and `+`: comparisons bind looser than arithmetic, and `a <= b == c` should probably be a parse error (non-associative at its own level) rather than either association silently.
- **`<`** comes along as `Lt(n, m)` (definable as `Le(Succ(n), m)`) if the kit wants it; don't add `>=`/`>` flipped forms until a use site asks — argument-order flips are exactly what [[method-receiver-position]] taught to be suspicious of.
- **Lexer care:** `<=` must not collide with the generics lexing of `<` (`Monoid<A>`); the tyargs path and the expression path need the usual disambiguation check.

Acceptance: `fuel_monotone` and the le-kit stated with `<=`; a parse-error negative control for `a <= b <= c`; a generics declaration still parsing in the same file.

## Log

- 2026-08-01: Landed: TokKind::LtEq in the lexer; NOT an infix_op row (those are left-associative by construction) — a new Parser::comparison rung extracted from the existing statement-level '=' handling, one non-associative level carrying =, <= (-> Le(a,b)) and < (moved off the table; 'lt' had no definition, so a<b<c chaining silently was pure hazard). Chains all reject with a real message; a <= b = c is the one unflaggable shape, blocked on [[annotated-let-swallows-the-equals]] (documented, docs/language/comparison-operators.md §3). Generics untouched (tyargs never see LtEq). lib restated: <= in stated positions, explicit Le kept in the four dense motives. +10 tests, full suite green, check time unchanged. Lt stays a one-row follow-on until a use site asks.
- 2026-08-16: 2026-08-16: The last line's prediction — 'Lt stays a one-row follow-on until a use site asks' — was wrong, and this issue's own 'Lexer care' bullet is why. It worried that <= must not collide with the generics lexing of <, and the landing round noted 'generics untouched (tyargs never see LtEq)'. The bare < is a different token and tyargs DO see it: Parser::ty read every 'ident <' as type arguments, so Lt was unwritable in any type position — h: i < len(xs) failed to parse. Fixed in [[nat-order-kit]]'s round by making that parse speculative (docs/library/nat-order-design.md §4); the < fallback name also moved from lt to Lt. Residue: [[comparison-inside-type-arguments]].
