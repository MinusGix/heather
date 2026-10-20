---
title: "split_all: split a match on decide<P>() (an evidence if) without ill-typed motives"
status: open
labels: [tactics,proofs,elaboration]
area: tactics
created: 2026-10-02
updated: 2026-10-02
---

A step's per-byte facts written over `if`-predicates, such as
`wc_step(s, b).lines = s.lines + Nat::of_bit(newline(b))` with `newline`
defined by `if b = '\n'`, need split_all to split through `decide`. Today it
does not:
- it recognises a match only at a reduct's head, so the BitVec instances'
  equation idiom `(match bit as λ c => (bit = c) → …)(refl)` hides the bit;
- `bitvec::BitVec::*_dec` decisions count as opaque word operations and are
  never unfolded.

Branch `s3-frontend-wip` (27a6364a) fixes both. Probes in which both sides
come from one definition pass (`st2(c, b) <= Succ(c)`, `st2(c, b) = c +
of_bit(nl2(b))`). But abstracting a bit inside a decision's proofs can give an
ill-typed motive, which the kernel refuses and the elaborator does not catch
([[native-frontend-decided-matches]] (a)). Before landing, either show the
motive stays well-typed for one-definition goals, or abstract at the decision
(`Inl`/`Inr`) and close the contradictory cases with `Reflects`.

The bundle default `advances` hits this for any step whose predicate uses
`∨`, `¬` or a decision. See also [[filter-default-spells-program-names]].

## Log

- 2026-10-02: 2026-10-02: an evidence-free `if` no longer goes through a decision: since [[native-frontend-decided-matches]] it is a match on the decision's bit (`b.eq_bit(10)`, `x || y`), which split_all splits like any Bool, so the per-byte facts and the bundle's `advances` default over `if`-predicates need nothing from this issue. What remains is a match on `decide<P>()` itself (`if h: P`, explicit decisions): abstracting a comparison inside the instance's proofs still gives an ill-typed motive. Lower priority; the WIP's `_dec` unfolding and applied-match changes were not landed.
