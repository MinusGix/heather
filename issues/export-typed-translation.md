---
title: Typed exporter with eta-long irrelevant terms and no holes
status: open
labels: [translation,export]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-20
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
