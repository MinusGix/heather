---
title: Typed exporter with eta-long irrelevant terms and no holes
status: open
labels: [translation,export]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-21
---

The prototype exporter (`crates/export`) is syntax-directed and prints
checked spellings (`pair@`, `inl@`, `fst@`, …) as prelude constants with
holes, which the target's elaborator fills. That is sound, because holes
appear only in proofs, but fragile: Lean's elaborator needed
`with_unfolding_all` for a conversion its kernel accepts
(`crates/export/probes/WfNative.lean`). It also cannot maintain the
invariant both targets need for Heather's irrelevant types
(`docs/export-fragment-design.md` §5.2): every term at a type whose whnf is
`sEq`, `sEmpty` or `Squash` must be written eta-long.

The round:

1. Walk each declaration with the kernel's inference (`heather_kernel::typing`),
   and erase each checked spelling to its component form at the whnf the
   derivation contains (`docs/intro-by-type-design.md` §2.4's `⌊·⌋`).
2. In the same pass, eta-expand neutrals at irrelevant types, and through
   `Σ`s whose components need it.
3. Keep sharing. Heather terms are DAGs, and a tree printer is exponential in
   the worst case. Emit Lean through its kernel (an `addDecl` import program,
   or the hash-consed export format) rather than as surface text.
4. Names: module-qualified Heather names instead of `g<index>` (decided by
   Minus 2026-10-21). The
   elaborator's `global_name_at` is crate-private today, so this needs a
   public accessor (or the names from module images, as in
   [[export-keeps-proofs]]).

Done when the prototype's acceptance test exports with no hole, Lean rechecks
it through its kernel without the elaborator, and `B::not_not`-shaped
declarations need nothing from the target's unifier.

## Log

- 2026-10-21 (PR #87): items 1 and 4 done another way, item 2 partly.
  Checked spellings are erased by the kernel's own `⌊·⌋`
  (`typing::spell_checked_in_code{,_ty}`) before translation, so the walker
  stays syntax-directed; a body whose spelling fails falls back to holes (two
  in the library sweep). Names are module-qualified, generated definitions
  included (`Elaborator::generated_key_at`: `bool::Bool#tycode`). For
  irrelevance the exporter prints the **canonical element** of a closed
  singleton type wherever it can read the type without inference (binder
  domains, global statements, application codomains, projections; design
  §5.2), and leaves types as written: collapsing the types to `Unit` made
  Lean reject an `inl` whose expected type reached the singleton only by
  δ-unfolding an open definition. What is left: neutrals at *open* types
  that become singletons by substitution (both targets), unit η in Rocq, and
  item 3. Printing with minimal parentheses was needed for Lean to parse a
  library-sized file in reasonable time; the kernel route of item 3 is still
  the real fix for size.
