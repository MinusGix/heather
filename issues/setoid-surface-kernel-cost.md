---
title: calc ≈ and rel_cong cost far more kernel steps than the terms they stand for
status: open
labels: [setoids,relations,elaborator,performance]
area: tactics
created: 2026-10-13
updated: 2026-10-26
---

Measured cold (`heather check --timings`: `eval_steps`, `decls_gated`) while
recasting `SameDefinedState` as a setoid ([[same-defined-state-setoid]]): the
setoid surface costs far more kernel work than the terms it stands for, and
the extra work grows with the declarations its generated source adds to the
gate.

One three-step chain, `after_left ≈ normal_left ≈ normal_right ≈ after_right`
(`execute_canonical_respects_defined`, `lib/std/arch/x86_64/x86_64.hthr`),
written four ways in one probe module:

- `trans(a, trans(evidence(…)(l, r, same), sym(b)))`: the baseline, one
  gated declaration.
- the same as `calc { … ≈ … }` with the evidence written: a few times the
  baseline's steps, five gated declarations.
- `trans` with `rel_cong(same)` for the middle step: over an order of
  magnitude more than the baseline.
- `calc` with `rel_cong`: the dearest, a dozen gated declarations.

The certificate `rel_cong` finds is the same `evidence theorem` written by
hand in the explicit forms, so the difference is the route (aliases, the
`relation_step` call through the `Transitive` view of the instance), not the
proof. In the x86 modules the change still nets out cheaper, because the
relation's own lemmas shrank by more; a client with many short chains would
not.

Wanted: `calc` over a relation whose dictionary is known, and `rel_cong`
with a resolved certificate, emit the term the explicit form is, and gate no
alias that the final term does not keep. Acceptance: the four forms above in
`crates/elab/tests` with item counters, `calc`/`rel_cong` within a small
factor of the explicit `trans`.

Related: [[relational-derivation-cost]] owns the search side of `rel_derive`
(certificate probes, family searches); this is the emitted term's cost at an
ordinary `rel_cong`/`calc` use with nothing to search.
- 2026-10-26: `rewrite(h, e)` along a relation ([[rewrite-setoid-relations]])
  emits its congruence and transitivity terms directly as kernel terms (no
  generated declarations). On one `Rat` calc step it sits between rel_cong
  and the explicit term: a few times rel_cong's eval steps per step (the
  extra is the occurrence conversion and the gate checking `app@` spines),
  well under the generated-source overhead this issue measured. rel_cong's
  own cost is unchanged.
