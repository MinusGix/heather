---
title: bv_decide: read word hypotheses from the context
status: open
labels: [bitvec,solver,tactics,feature]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

`bv_decide` reads only the goal. Program proofs need conditional facts ("if the byte is a continuation byte, then …"): read hypotheses `h: p = True` (and `a = b` between words) over the same atoms into the predicate as `PNot(h) ∨ goal`, and discharge them in the read-back by the hypotheses themselves.

Parent: [[lrat-certified-bitvector-decision]].
