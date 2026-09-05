---
title: Lift subtype operations and compare evidence policies
status: open
labels: [stdlib,subtypes,proofs,transfer,design]
created: 2026-09-04
updated: 2026-09-05
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

## Signature-directed inheritance

`docs/smart-subtype-inheritance.md` distinguishes adapting input positions,
strengthening a selected result, and suggesting a new conditional API. Use an
explicit target signature for lifting; an ambient return carrier alone is not
enough to choose a subtype result. Preserve source hypotheses and expose
unproved result invariants as resumable goals. Adding a caller premise requires
an explicitly chosen conditional signature, never silent contract strengthening.

Exercise mixed ambient/subtype inputs and two adaptations of natural
subtraction: a Nat result without a new positivity requirement, and a positive
result under a proved sufficient condition. Domain obligations for intermediate
applications must remain visible in transferred conditional laws; such an
operation does not satisfy a total semigroup interface automatically.

The first generator slice remains the explicit positive-addition wrapper and
projection theorem. Automatic signature discovery and conditional suggestions
are later work, not requirements for that first slice.

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

- 2026-09-05: Started [[packaged-subtype-representation]] to share representation
  ingredients and exercise existing Omega closure. It exposed
  [[omega-local-proof-aliases]], [[omega-certificate-imports]], and
  [[lambda-predicate-index-inference]]; these remain separate follow-ups.
- 2026-09-05: [[packaged-subtype-representation]] completed: one representation
  supplies both lift interfaces, with resumable closure and a checked Omega
  customer. Full Furnace suite: 2,375 passed, 0 failed, 5 ignored. Automatic
  fact collection and broader closure discovery remain open.

- 2026-09-05: Started [[explicit-subtype-code-template]] for the binary wrapper
  and projection proof. Automatic closure search and broader transfer remain here.
- 2026-09-05: [[explicit-subtype-code-template]] completed with Heather templates,
  explicit closure evidence, and resumable goals. Final Furnace suite: 2,374
  passed, 0 failed, 5 ignored. This closes the explicit emission slice; automatic
  ingredient/closure discovery and the broader evidence-policy work remain open.

- 2026-09-04: Filed from the setoid and general transfer design discussion.
- 2026-09-04: Added the tiny positive-natural experience and its proposed expected-result adaptation, with an explicit squash-preserving expansion.
- 2026-09-05: Started [[positive-subtype-manual-round]]: an explicit positive-natural record, closure proof, and inherited semigroup laws provide the first checked customer. This manual round uses relevant evidence and value-based comparison; wrapper generation and the broader evidence-policy comparison remain here.
- 2026-09-05: The first explicit customer is complete in [[positive-subtype-manual-round]]: positive addition and semigroup laws check, with resumable closure goals and value-based comparison. Automatic result construction, heterogeneous/general transfer, evidence-policy comparisons, and cost measurements remain open here.
- 2026-09-05: Added docs/showcase/witness_subtype.hthr and docs/witness-subtype-round.md: a relevant upper-bound witness computes through binary lifting; addition respects value equality, while a checked counterexample rules out a bound-reading observer under that relation. Evidence-policy comparisons and general dependent transport remain open.
