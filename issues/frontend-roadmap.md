---
title: "Meta: frontend roadmap and current focus"
status: open
labels: [frontend,meta]
created: 2026-07-23
updated: 2026-07-23
---

Organizing issue for the frontend push (the frontend-first route,
[[elaborator-design]]). The point of this issue: keep the *focus order*
here so the per-topic issues stay granular and jumpable — pick any issue up
without re-deriving where it sits.

Design record: [[surface-syntax]] (decisions) + docs/sketches/surface-v0..3
(the reasoning); requirements tracker: [[front-end-sugar]].

## Focus order (edit as reality intervenes)

1. ✅ Stage 1: parser + annotation-filling elaborator; Nat suite checked
   ([[elaborator-design]], [[stress-proof-suite]] item 1).
2. [[metatheory-ch07-pass]] — interleave; wants doing before tier-1
   inductives generate serious term volume on the extension formers.
3. [[elab-stage2-metas]] — implicit annotations/levels; the Nat suite loses
   its explicit motives and endpoint spam. Unblocks most ergonomics.
4. [[surface-operators]] — `+`/`==` operators, method calls, `calc`.
   Mostly parallel to 3; lemma-application ergonomics.
5. [[match-recursion]] — termination checking; `induction`/`rec` collapse
   into `match` with IH = self-call.
6. [[goal-holes]] — `?holes` + `on` discharge (needs stage-2 metas).
7. [[inductive-compiler]] tier 0 → List hand-prototype → tier 1
   ([[stress-proof-suite]] item 2).
8. Tier 2 / `Acc` by hand ([[stress-proof-suite]] item 3), then reopen
   [[ir-simulate-design]] in-language.

Later, tracked where linked: implicit quotation + modal surface
([[surface-syntax]] round 2), context-specific compilation / certified PE
([[compile-typeclass-design]], [[certifying-generator]] — sketch round 3),
goal-solver meta-functions (sketch round 3 §2).

## Log

- 2026-07-23: Opened after stage 1 landed, alongside the granular issue
  split (stage2/match-recursion/goal-holes/surface-operators/ch07-pass).
