---
title: "Direct ≠ notation for negated equality"
status: closed
labels: [frontend,syntax,notation,logic,stdlib,ergonomics]
created: 2026-08-20
updated: 2026-08-20
---

Add `a ≠ b` as direct notation for `¬(a = b)`. It should desugar to the
existing negation and equality forms, not introduce a separately named `Ne`
relation whose qualification, instances, or reduction behavior could drift
from the proposition it abbreviates.

`≠` belongs at the comparison rung with `=`: non-associative, tighter than
`¬`, `∧`, and `∨`, and usable wherever equality is currently accepted. The
Unicode token is the language spelling; editor input such as `\ne` is tooling,
not a second semantic form. An ASCII `!=` alias is deliberately not required
by this issue.

## Acceptance

- `a ≠ b` produces the same surface/core proposition as `¬(a = b)`, without a
  new library declaration.
- Precedence is pinned for `a ≠ b ∧ P`, `¬(a ≠ b)`, and rejection of chained
  comparisons.
- Expected-carrier equality resolution behaves identically under both
  spellings, including open polymorphic endpoints.
- Nat, Int, Bool, and List public statements adopt `≠` where it improves
  readability.
- Diagnostics and pretty-printing prefer `≠` when the written/source form is
  available without disguising arbitrary functions into `False` as inequality.

## Log

- 2026-08-20: Filed from the standard-library review with the direct-desugaring
  direction chosen specifically to avoid a second nominal relation.
- 2026-08-21: Landed as one Unicode lexer token and a comparison-rung parser
  case which emits the exact `Not(a = b)` surface tree; no declaration,
  resolver path, or kernel form was added. Precedence, non-associativity, the
  absent `!=` alias, and agreement at open polymorphic endpoints are pinned.
  Surface diagnostic rendering recognizes only the preserved `Not(Eq)` shape
  as `≠`, never an arbitrary function into `False`. Nat, Int, and Bool
  public equality-refutation statements were respelled; List has no public
  negated-equality statement to migrate, so no unrelated API was invented.
  Full workspace suite green.
