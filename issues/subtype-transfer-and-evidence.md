---
title: Lift subtype operations and compare evidence policies
status: open
labels: [stdlib,subtypes,proofs,transfer,design]
created: 2026-09-04
updated: 2026-09-04
---

Make closure under an operation sufficient input to generate the corresponding
subtype operation and eligible inherited laws. Use a heterogeneous relation
between ambient values and subtype contents as the transfer interface.

## Acceptance

- Lift addition to positive naturals from closure and obtain a semigroup.
  Diagnose why zero cannot supply an additive monoid unit for this subtype.
- Generate projection/computation lemmas and transfer a reusable theorem with
  its domain hypotheses intact.
- Compare three evidence policies on the same customer: ordinary relevant
  proofs with a relation ignoring evidence; squashed invariant fields; and
  elaborator reuse/unification of evidence when valid.
- For evidence reuse, distinguish solving an unassigned proof metavariable
  from replacing an already fixed proof. Replacement must be justified by
  conversion, equality with required dependent transport, or an explicit
  representation transformation. Do not add arbitrary proof identification.
- Test an operation depending on a witness and a type depending on that
  witness. An evidence-ignoring relation only supports functions certified
  independent of the ignored evidence. Squashing must respect elimination
  restrictions; it cannot preserve arbitrary witness-consuming operations.
- Measure reconstruction, casts, generated term size, and checking cost.
  Decide when to recommend squashing or shared evidence; neither is an
  automatic global policy yet.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns the ambient/subtype correspondence rules.
- **[[sprop-squash]]** owns Squash and its restricted elimination rules.
- **[[squash-library-api]]** owns ordinary squash combinators.
- **[[dependent-relational-transport]]** owns general dependent fiber transport.
- **[[setoid-auto-lifting]]** owns the eventual wrapper/proof generator.

## Expected-result construction probe

The `twice` experience in `docs/three-small-transfer-experiences.md` uses an
explicit `.value` projection and an expected subtype return type. Generate the
wrapper/evidence at that boundary, with a registered positivity lemma as the
first solver; no global arithmetic coercion mechanism is needed.

The proposed subset syntax provisionally means a value with a squashed
condition. This is a candidate policy for that constructor, not a change to
ordinary proof-relevant records. Lower `twice` using `squash_map` and a closure
lemma; do not unsquash the input evidence into a relevant local hypothesis.
The exact result obligation is squashed. The UI may separately request the
sufficient ordinary closure lemma and must distinguish those routes.

Check success, missing-lemma feedback, and the invalid constant-zero result.
Users who need to compute from evidence retain an ordinary relevant record/Σ.
This probe does not settle all subtype evidence policies.

## Log

- 2026-09-04: Filed from the setoid and general transfer design discussion.
- 2026-09-04: Added the tiny positive-natural experience and its proposed expected-result adaptation, with an explicit squash-preserving expansion.
