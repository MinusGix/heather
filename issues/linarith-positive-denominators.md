---
title: linarith: clear positive denominators from facts and goal
status: open
labels: [tactics,arith,reals]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

`linarith` (docs/linarith-design.md) reads a reciprocal as an atom, so a fact
or goal whose content is the inequality behind a fraction is out of its
reach: `a * d⁻¹ <= b` with `0 < d` is `a <= b * d`, but to the search
`a * d⁻¹` is one atom unrelated to `a`. [[field-simp]] left this form to
[[linarith-ordered-fields]], which closed without it.

Shape: when a row mentions a reciprocal atom `r` whose denominator `d` has a
positivity fact (written, in context, or by construction as for
`Rat::inv_succ(n)` with `Rat::inv_succ_pos`), offer the search the row
multiplied by `d` as well, its linear form reduced by `r·d = 1` (the fact
`ring` already reads with the reciprocal). The certificate side is there:
`lin_scale_le`/`_lt` take any positive factor with its proof, and the
identity is `ring`'s, which clears `r·d` itself. The goal's negation is
scaled the same way.

## What it assumes from elsewhere
- **[[linarith-ordered-fields]]**: the reading and the part lemmas.
- **[[field-simp]]**: the reciprocal facts `ring` reads (`<op>_mul`,
  `Rat::inv_succ_cancel`).
