---
title: `++` for list append: lexicon addition, and the `+` at List designation reviewed
status: closed
labels: [frontend,syntax,stdlib,ergonomics]
created: 2026-08-09
updated: 2026-08-10
---

`xs + ys` for concatenation reads as a pun the same way `+` = or at `Bool` did
([[bool-operator-designations]]), and the answer is the same shape: give the
operation its own programming spelling, `++`, and retire the designation that
made a symbol with arithmetic connotations mean something else.

**The addition.** `++` is a curated lexicon entry on the `&&`/`||` recipe —
[[notation-extensibility]]'s log (2026-08-09) prices it at ~4 small edits:
lexer token, binding-power row, `op_symbol`, and the designation change below.
Like the doubles it postdates the fixed table, so it gets **no fallback rung**:
away from a designation or a binder it refuses, and the two designation rows
are the whole of what it means.

**Design points to settle (small):**

- **Precedence.** `+`'s own level is the natural pick (it is the same
  associativity story); the doubles chose *below* `+`/`*` for the theorem-
  statement reading, but `++` is not propositional, so the arithmetic level
  looks right. Decide with an example in hand.
- **Lexing.** `++` must lex before single `+` (two-byte window first, as
  `&&` does); `x++` with no space is the case to test.

**The designation review.** `designation<A> + at List<A> := append` is
replaced by the same row under `++`. Consequences, eyes open:

- `concat` leaves `sum_all` (which is bound to the symbol `+`) and becomes
  `mconcat(append, xss)` — positional, one word, beside `any_of`/`all_of`,
  and for the same reason: the operation's carrier no longer designates the
  fold's symbol. There is no `++`-fold beside `sum_all`, for the reason there
  is no `&&`-fold: one fold per symbol is the duplication this line of design
  deletes.
- Bare `xs + ys` at a list then falls to rung 3 (`+` → `add`) and fails to
  *check*, not to resolve. Worth a look at the diagnostic: the refusal should
  read as "no designation for `+` at `List`" territory, not a confusing
  `add`-expects-`Nat` type error.

Only `lib/std/algebra.hthr` uses the List designation today, so the library
edit is one file.

**Acceptance:** lib restated with `++`; a negative control for bare list `+`
with a readable diagnostic; `x++` lexing test; parser tests for the token in
designation, binder, and applied positions; full `scripts/test`.

## What it assumes from elsewhere

- **[[notation-extensibility]]** owns the user-extensible-lexicon question.
  Assumed here: only that curated additions remain the interim policy.

## Log

- 2026-08-10: LANDED: `++` is a two-byte operator at additive precedence with no fallback; `List<A>` designates it as `append`, `concat` is positional, old List `+` retains a fallback-aware diagnostic, and parser/elaborator/library controls cover adjacency, binders, designations, literals, neutrals, and refusals. Full `scripts/test` green.
