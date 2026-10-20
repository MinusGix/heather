---
title: Keep theorem proofs available to the exporter
status: open
labels: [translation,export]
area: language
milestone: [export-fragment]
code: crates/elab/src/lib.rs:4150 @ 95a125b
created: 2026-10-20
updated: 2026-10-20
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
