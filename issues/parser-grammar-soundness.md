---
title: Prove calculator recognition against an independent grammar relation
status: closed
labels: [stdlib,parsing,proofs]
created: 2026-09-14
updated: 2026-09-15
---

## Problem

The parser library has operation-indexed `Sound` certificates and checked
rules for recognition, mapping, bind and choice. The migrated calculator has
its AST/error examples and open-input compiler agreement theorem. Neither
constitutes a proof that every successful calculator parse has a derivation
in an independently stated grammar.

## Scope

State a source-span grammar relation fixing precedence, right association,
and parentheses. Use the library's compositional postcondition rules and a
checked recursive argument to establish success soundness for the three
precedence levels and complete entry point. Keep the relation independent of
calling the implementation to decide membership. Prove the consumed-span
connection, not only a property of the resulting AST.

Completeness requires its own explicit ordered-recognition policy and branch
conditions; do not infer it from success soundness or claim general ordered
choice explores every derivation. Decide its scoped theorem after soundness.

## Acceptance

- Open token-stream success implies the independent grammar relation.
- Malformed spans, wrong precedence and left-associated replacements do not
  acquire proofs through a vacuous or implementation-defined relation.
- Preserve the existing calculator examples and compiler agreement.
- Audit any recursive proof's assumptions; no new unchecked axiom.

## What it assumes from elsewhere

- [[parser-combinator-library]] owns the executable library and compositional
  certificate interface; this issue owns the additional calculator theorem.

## Log

- 2026-09-15: Implemented independent `Derivation`, structural `spelling` and
  `meaning`, and `WellFormed` production levels. `Grammar` connects an arbitrary
  start/end cursor to the exact consumed prefix and suffix; `WholeGrammar`
  requires the derivation to spell the complete source.
- 2026-09-15: The recursive parser constructs `Certified` successes. Projected
  public replies retain the original signature, AST/error examples and compiler
  agreement. `grammar_sound`, `factor_sound` and `atom_sound` provide the three
  relations; `expression_sound` exposes open-prefix recognition and `parse_sound`
  proves the whole-input success implication. This route needs no generated
  mutual unfolding equation or new axiom.
- 2026-09-15: Added generic certified recognition, exact selected-head suffix
  evidence, certificate projection/composition laws and `complete_sound` to the
  parser library. Flattened `Certified` fields and generic `result::fold` keep
  concrete production composition checkable under the existing memory rail.
  [[parser-certified-composition-cost]] owns the remaining checking cost;
  [[parser-certificate-ergonomics]] owns simplifying the verbose proof client.
- 2026-09-15: Focused acceptance: **5 passed, 0 failed**. It includes independent
  open-numeral/open-suffix witnesses, open parse and cursor-span theorems, six
  malformed-derivation controls, prior false-result controls, empty axiom
  reports, and the unchanged depth-1/2/4/8 cases. The depth sweep now shares the
  calculator image, removing one duplicate Rust test/build without removing cases.
- 2026-09-15: Completeness decision: do not add a general ordered-recognition
  completeness claim in this round. [[parser-canonical-printers]] must establish
  executable acceptance of its generated subset; grammar soundness alone is
  insufficient for that reverse direction. Design and proof notes are in
  `docs/calculator-grammar-soundness.md`.

- 2026-09-15: Final full `scripts/test`: **2672 passed, 0 failed, 5 ignored**. Tracker and whitespace checks pass. The one-test count reduction is the retained depth sweep sharing the calculator fixture. All acceptance items are complete; remaining ergonomics/checking cost and canonical-printer recognition laws have separate owners.
