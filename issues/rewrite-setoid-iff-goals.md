---
title: Rewrite along a relation inside ↔ goals
status: open
labels: [setoids,relations,tactics,proofs]
area: tactics
milestone: [tac-general]
created: 2026-10-26
updated: 2026-10-26
---

`rewrite(h, e)` along a relation ([[rewrite-setoid-relations]],
`docs/tactics/equation-rewrite-design.md` §9.2) rewrites relation applications and
implications between them, at either polarity. A `P ↔ Q` goal is refused
today: `Iff` is a record, so the plan would have to project `e`'s `mp`/`mpr`,
emit the `→` plan for each direction (each half once forward, once
backward), and rebuild with the constructor, around kernel terms that may sit
under the λs an implication's plan introduces.

The pieces exist: the `→` plan already emits both polarities, so `P ↔ Q`
backward is `Iff(mp := λ p. Q-back(e.mp(P-forward(p))), mpr := λ q.
P-back(e.mpr(Q-forward(q))))`. What is missing is reading `P` and `Q` off a
monomorphized `Iff<P, Q>` type and building the record value and its
projections as kernel terms at a depth below the context.

`↔` is rare in `Rat`/`CReal` today (`nat.hthr` and `int.hthr` use it); this
waits for a customer.
