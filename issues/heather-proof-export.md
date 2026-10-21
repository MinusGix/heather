---
title: Export a closed fragment of Heather proofs to Coq or Lean
status: open
labels: [translation,metatheory,design]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `export-fragment` milestone (`docs/roadmap.md`):
translate Heather proofs and their dependencies into Coq or Lean, so they
can be checked outside Heather.

Export is the easy direction for most proofs: Heather is predicative and has
no K, so a proof that avoids the DeLaM code layers and `sEq` asks less of its
target than Coq or Lean provide. Equality can be translated with a
replacement symbol where the two theories differ. The first round:

1. Pick the target (Coq is closer to heather-coq's formalization of the
   kernel; Lean is where Minus's other projects live).
2. Translate a closed fragment, such as the Nat and List lemmas, from kernel
   terms (not surface syntax), and recheck it there.
3. Record which kernel features stopped the translation, as the list a
   trusted-fragment theorem would later have to cover.

## Log

- 2026-10-20: exploration round. Design: `docs/export-fragment-design.md`;
  prototype `crates/export` (kernel Ψ → HX → Lean and Rocq printers, two
  hand-written preludes) with `scripts/export-recheck`; probes in
  `crates/export/probes/`. On a Nat-and-enum slice, Lean 4.20 checks all 22
  declarations and Coq 8.18 checks 20. Coq stops at unit η and at unary
  numerals. Decisions proposed, pending Minus: **Lean is the first target**
  (step 1 above). Translate from kernel terms through HX (step 2). The stops
  (step 3) are §6 of the design. Follow-ups: [[export-keeps-proofs]],
  [[export-typed-translation]], [[export-library-sweep]],
  [[export-wf-native-inductives]], [[export-checks-theorem]]. Rocq as a full
  second target is parked here until unit η is answered (design §5.3).
- 2026-10-21: Minus decided: Lean first; module-qualified exported names.
  The open-tag β side condition is recommended to stay an exporter-side
  condition measured by [[export-library-sweep]] (design §11.3); Minus
  agreed.
