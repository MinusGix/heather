---
title: linarith: clear positive denominators from facts and goal
status: closed
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

## Log

- 2026-10-27: Built (docs/linarith-design.md §5). ring's FieldReading keeps each reciprocal's denominator (ring::Reciprocal); a denominator is a factor when a strict fact's difference is d (0 < d) or r (0 < x⁻¹, via lin_den_pos with ring's identity); Rat::inv_succ(n) brings Rat::inv_succ_pos(n) as a fact. Rows mentioning r — facts' and the goal's negation — are also offered multiplied by d with r·d read as 1, up to two denominators per row; the goal's multiplier becomes a positive term K = Σ λⱼ·Pⱼ, and ring checks the identity modulo the reciprocal facts. Probes at Rat and CReal in lib/_tests/std/tactic/linarith_tests.hthr, unknown-sign and negative denominators refused.
