---
title: IH generalization: recursion whose non-decreasing arguments vary
status: open
labels: [frontend,elaboration,design]
created: 2026-07-31
updated: 2026-07-31
---

Promoted from [[match-recursion]]'s deferred note (2026-07-24: "the one
real limitation") to its own jumpable issue, because it now has a named
customer waiting: \`fuel_monotone\` — [[ir-simulate-design]] section 11
item 3, the keystone of the converges interface — is an induction on fuel
whose motive must quantify env/ir/the equation, i.e. exactly this.

The mechanism, as the deferred note already sketched: M(z) = Pi over the
varying params; arm bodies lambda-wrap; self-calls become \`ih(e)\` at the
varied arguments; the match is forced to the body root. The MVP is the
empty-generalized-set case, so this is additive.

What the ir_v1 round adds to the picture:

- The WORKAROUND exists and is load-bearing today: return a function
  (\`lookup(env) -> Nat -> OptVal\`, fuel-curried \`eval\`). Fine for
  programs; for PROOFS it contorts statements, and fuel_monotone wants
  the theorem stated over the applied form.
- The manual route also exists — explicit motive
  (\`match fuel as λ f => (env: Val) -> ...\`) with the \`Succ(k, ih)\`
  arm spelling — so this issue's feature is "the elaborator computes
  that motive", not new power. A session-sized proof either way; the
  feature removes the motive-writing, not the case analysis.
- Cost coupling: generalized motives are bigger terms at every arm, and
  [[simulate-conversion-cost]] bills term size per conversion step —
  worth measuring on the fuel_monotone prototype rather than assuming.
