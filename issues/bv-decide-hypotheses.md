---
title: bv_decide: read word hypotheses from the context
status: closed
labels: [bitvec,solver,tactics,feature]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

`bv_decide` reads only the goal. Program proofs need conditional facts ("if the byte is a continuation byte, then …"): read hypotheses `h: p = True` (and `a = b` between words) over the same atoms into the predicate as `PNot(h) ∨ goal`, and discharge them in the read-back by the hypotheses themselves.

Parent: [[lrat-certified-bitvector-decision]].

## Log

- 2026-11-17: built: every local the reader can take (the goal's claim shapes, including `<`, `<=`, `≠` between words) joins the predicate as `¬h ∨ goal`; the rest are passed over. The read-back peels each with `layout_imp`, discharged by `layout_*_hyp` (lib/std/tactic/bitblast.hthr). A counterexample meets every hypothesis. Probes in lib/_tests/std/tactic/bv_decide_tests.hthr (`lt_trans`, `le_antisymm`, `eq_hyp`, `ne_hyp`, `bool_hyp`, `skips`, `lt_not_enough`).
