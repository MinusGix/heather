---
title: Keep theorem proofs available to the exporter
status: closed
labels: [translation,export]
area: language
milestone: [export-fragment]
code: crates/elab/src/lib.rs:4150 @ 95a125b
created: 2026-10-20
updated: 2026-10-21
---

A theorem commits as an opaque `GlobalBinding::Tm`, and its proof is kept
in Ψ only when the statement carries data (`sealing::carries_data`, the
sealed-proof route of [[theorem-witness-unfolding]]). Every other proof is
checked and dropped. The exporter (`docs/export-fragment-design.md` §1, §7)
therefore sees most library theorems as assumptions. The prototype writes its
lemmas as `fn`s to get around this, and the prelude's `sym`/`trans`/`cong`
export as axioms (Lean's `#print axioms` on `Nat::add_assoc` names
`Nat::cong_succ`).

Two routes, to be decided by whichever is cheaper to keep correct:

1. **An export mode on the elaborator** that records `(abs, proof)` beside
   Ψ at `commit_decl`. It must *not* go through `GlobalCtx::seal`: sealing a
   proof makes it unsealable at a stuck elimination and could change
   verdicts, while export only needs to read it.
2. **Read proofs from module images**, which already keep what replay
   rechecks (`docs/semantic-module-images-design.md`). This puts the exporter
   on the persisted, checked artefact rather than on a live elaborator, and
   needs no elaborator change, if images keep every proof.

Done when the library sweep ([[export-library-sweep]]) exports theorems
with their proofs and only explicit `axiom`s as assumptions.

## What it assumes from elsewhere
- **[[heather-proof-export]]** owns the export milestone. Assumed here: only
  that the exporter reads closed kernel declarations from Ψ.

## Log

- 2026-10-21: route 1. `Elaborator::keep_proofs_for_export` (or
  `with_prelude_for_export`) turns on a side table `abs -> (statement,
  proof)` filled at `commit_decl`; `export_proof(abs)` answers only while the
  binding is still that body-less statement. Nothing is sealed, so verdicts
  cannot move, and the mode is off by default. The prototype's lemmas are
  theorems again and the Lean output has no axioms
  (`crates/export/tests/nat_fragment.rs`); the library sweep exports
  theorems with their proofs ([[export-library-sweep]]). Route 2 (images)
  stays the shape for a CLI-level `heather export`, which would then not need
  a live elaborator.
