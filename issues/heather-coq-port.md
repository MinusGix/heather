---
title: Port heather-coq into Heather: a copy of the metatheory, by rungs
status: open
labels: [metatheory,design]
area: mathematics
milestone: [math-metatheory]
created: 2026-10-24
updated: 2026-10-25
---

heather-coq is the primary formalization of Heather's metatheory. Minus
asked (2026-10-24) for a copy written in Heather, for experience writing
metatheory in Heather and for the tools that writing it would force.
Heather-in-Heather would then state its theorems relative to the copy.

The assessment is `docs/heather-coq-port-assessment.md`. In short:

- **The hard limit (§3).** heather-coq's semantic half (the logical
  relation and everything after it) amounts to a consistency proof for
  Heather's own kernel, and it leans on Coq's impredicative `Prop`. Heather
  is predicative, so by Gödel the copy carries that half only for fragments
  weaker than Heather: no object universe, or k universes written stage by
  stage. Heather-in-Heather cites heather-coq for the rest.
- **The language blockers (§4).** [[mutual-inductive-declarations]],
  [[indexed-infinitary-families]], [[iwf-inversion-recursive-index]] and
  tier-3 inversion (`docs/iwf-former-design.md` §8.3), plus the scale of a
  90-constructor syntax and a 236-rule judgment.
- **The automation gap (§5).** About 3,000 `auto`/`eauto`, 425
  `inversion`s, and generated rewrite tables, against no proof search in
  Heather. This is `tac-general`'s work.

The proposed rungs are in doc §9: a syntax and reduction slice; typing and
the syntactic metatheory; a relation with no universe (the milestone's
current "done when"); one universe; and algorithmic conversion with the
bridge to `hih-kernel-model`.

## Log

- 2026-10-24: Opened with the assessment. Nothing is ported. The doc's §10
  lists the decisions that are Minus's.
- 2026-10-25: Two blockers landed: [[mutual-inductive-declarations]] (#163)
  and [[indexed-infinitary-families]] (#166). The assessment is revised
  after `docs/definitional-inversion-survey.md` (PR #173). Injectivity,
  subject reduction and progress have a proof without normalization, so
  they are not behind the Gödel limit. The doc's new rung 2b is that proof.
  Algorithmic soundness needs only injectivity, subject reduction and four
  layer-M equations (doc §6).
