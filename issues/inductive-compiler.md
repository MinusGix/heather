---
title: "Inductive declaration compiler: tiered encodings"
status: open
labels: [frontend,elaboration,inductives,design]
blocked-by: [elaborator-design]
created: 2026-07-23
updated: 2026-07-23
---

Mechanize the encoding doctrine of [[kernel-v1-extensions]]: surface
`inductive` declarations compile to the fixed-former kernel. This is the
load-bearing design object of the frontend — needed identically by the
stress proofs, the IR, and everything after — and the one frontend
component whose bugs prove theorems about the *wrong type* rather than
producing rejected terms. Hence the hard rule: **each tier's lowering is a
written mechanical scheme** (like the recursor telescopes), reviewable
against the kernel. The compiler stays untrusted (kernel checks its
output), but "user proved a theorem about an encoding that isn't what they
meant" is a failure the kernel cannot catch.

Pipeline: parse decl → positivity check → tier classification → generate
(type encoding, constructors, eliminator, no-confusion) → emit core.

## Tier 0 — non-recursive (Bool, Option, most IR node shapes)

Plain sums-of-Σs: tags are nested `A + (B + …)`, fields are right-nested Σ.
`match` = nested `case`; no-confusion (constructor injectivity +
disjointness) by large elimination into `Unit`/`Empty` — the Tarski setup
gives large elim since motives land in `Ty l` encodings. Entirely
mechanical; do first.

## Tier 1 — recursive finitary (List, the IR expression knot)

Nat-fording. **The one research-adjacent spot in the frontend plan.** The
dragon: a naive depth-*bound* encoding (`Σ n. Approx n`) has equality finer
than the intended type — `nil` at bound 3 vs bound 5 are distinct pairs;
that reinvents the setoid problem and would drag [[setoid-auto-lifting]] in
early. Committed fix: **exact-height fording** — constructors compute their
precise height (length for List, max+1 for trees; always computable in the
finitary tier), so canonical forms are unique and definitional equality is
the intended one. Eliminator by `elim_Nat` on the height, `elim_Empty`
discharging impossible cases; β on canonical constructors is definitional
(heights are concrete numerals there); open scrutinees are neutral, as
they should be.

**Hand-prototype List before writing the generator** — it is the
acceptance test of the whole tier ([[stress-proof-suite]] item 2).

## Tier 2 — infinitary (Acc, inductive families)

W + Id + funext-as-axiom via the standard indexed-containers reduction
(argued in [[kernel-v1-extensions]]; first-order data never lands here).
Generator support can lag; a hand-built `Acc` exercises the synthesized-ih
β rule ([[stress-proof-suite]] item 3).

## Scope notes

- Parameters: straightforward (prenex, substituted through the scheme).
- Indices: via fording (Id equations on constructor results) — design the
  tier-1 scheme so indexed finitary types are the same machinery, not a
  fourth tier.
- Derived per-inductive artifacts (recursor, no-confusion, later:
  size/height lemmas) are generated *terms* checked by the kernel —
  auditable, never trusted.

## Log

- 2026-07-23: Opened; tiers, exact-height decision, and the
  List-prototype-first discipline from the frontend-first route discussion.
