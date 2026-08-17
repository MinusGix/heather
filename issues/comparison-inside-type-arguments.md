---
title: "A `<` nested directly inside type arguments needed parentheses"
status: closed
labels: [frontend,syntax,parser]
created: 2026-08-16
updated: 2026-08-16
---

**CLOSED 2026-08-16, the same day it was filed** — `Or<n < m, m <= n>` parses.
The fix is the one-directional whitespace rule
(`docs/type-argument-disambiguation.md`): a `<` with a space before it never
opens a type-argument list, so the inner ` < ` cannot steal the outer's `>`.
Parentheses still work and are still the documented escape; they are simply no
longer mandatory. The body below is the problem as filed.

---

`Or<n < m, m <= n>` does not parse. `Or<(n < m), (m <= n)>` does, and so does
every other position a comparison can appear in as a type — the parameter
`h: i < len(xs)`, the result `theorem b(n: Nat): n < Succ(n)`, and arbitrary
nesting once the parentheses are there.

This is the deliberate residue of the `<`-in-type-position fix
([[nat-order-kit]], landed 2026-08-16; `docs/nat-order-design.md` §4). That
fix made `Parser::ty` **speculate**: read `ident <` as type arguments, and if
the parse does not complete, rewind and let the expression grammar have it. It
covers every case where the failure is visible to the *outer* parse. It does
not cover this one, because the inner `self.ty()` parsing the argument `n`
returns successfully at `n` and the outer loop then demands a `,` or `>` and
finds `<` — the argument parse *succeeded*, just short, so there is nothing for
the outer rewind to catch.

## What a fix looks like

The argument grammar would have to admit a comparison — i.e. inside type
arguments, parse each argument at a rung that includes the comparison
operators, accepting that `>` is then ambiguous with the closing bracket. That
ambiguity is the reason it was not done in the landing round: `A<B > C>` has
two readings and neither is obviously wrong, and the `>`/`>=` symbols are
deliberately not in the language yet ([[nat-order-kit]] holds them back until a
use site asks). Whichever way it is resolved, the resolution should be made
*once*, for `>` as an operator and `>` as a bracket together, rather than
twice.

## Why it is not urgent

The position that mattered is the hypothesis — `h: i < len(xs)`, which is
`Lt`'s reason to exist ([[guarded-to-option-adapter]],
[[surface-fin-indexing]], [[termination-measures]]) — and that works. A
comparison nested inside type arguments arises where a connective is applied to
two comparisons, and `Or<(n < m), (m <= n)>` is a legible spelling of that. The
cost is two characters and a reader's momentary "why".

## What it assumes from elsewhere

- **[[nat-order-kit]]** owns the propositional order that made `<` a type at
  all. Assumed here: only that `n < m` is a type and is written where a
  hypothesis is.
- **[[surface-operators]]** owns the symbol ladder. Assumed here: only that
  `>` and `>=` are not yet in the language, which is what makes the bracket
  ambiguity a future decision rather than a present one.

## Log

- 2026-08-16: Filed from the wave-1 round, which fixed the larger half of the
  same ambiguity and left this measured rather than assumed — the failing and
  passing spellings above were both run through the CLI.
- 2026-08-16: CLOSED by docs/type-argument-disambiguation.md. This issue's own 'what a fix looks like' section was wrong about the fix and about the difficulty, and the correction is the finding. It proposed admitting comparisons into the argument grammar; that does NOT work, because the failure is not that the inner comparison is unparseable — it is that the inner ident+< SPECULATES AND SUCCEEDS, eating the outer list's closing >. Verified directly: Or<n < m, Nat> reported '`Or` cannot be used here', i.e. the outer had already rewound to an expression. Nor is per-argument retry available: Or<Option<Nat>, n < m> needs inner speculation ON for its first argument and Or<n < m, Option<Nat>> needs it OFF for its first, so the choice is per argument and the combinations are exponential. Complete disambiguation by backtracking alone needs GLR/Earley, which is why every <>-keeping language wants a marker here. What actually fixed it was supplying the one bit backtracking cannot recover — which <s are ELIGIBLE to be brackets — via whitespace, one-directionally, so that no program that parsed before parses differently. The > ambiguity this issue deferred to a future >/>= decision is now a recorded commitment instead (design §6): > stays a non-operator, and the escape if ever wanted is the distinct token ≥.
