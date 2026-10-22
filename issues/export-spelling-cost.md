---
title: Spell ordered_field's proofs for export within the rails
status: closed
labels: [translation,export,performance]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-21
updated: 2026-10-22
---

The whole-library sweep (`crates/export/tests/library_wide.rs`, design
§5.6 and §7) leaves out `ordered_field` and the modules that import it
(`rat`, `creal`), because spelling their proofs for export costs too much.
The translation, the hash-consing and the node table are cheap there now;
what is left is `⌊·⌋` (`typing::spell_checked_for_export`).

Its eager checker walks a term as a tree, and in this module every
theorem's first binder is the class `OrderedField(≈, <, <=, +, *)`, whose
record type it re-checks with all its fields' statements. That is tens of
seconds a theorem, and `OrderedField::one_apart_zero` (a one-line proof)
runs past the 6 GiB address-space rail in it.

Routes, cheapest first:

1. A formation memo in the spelling pass, keyed by node and Γ. Tried
   2026-10-21 with Γ's identity token, it did not move: the tree walk
   re-enters binders, so Γ is a new node at every visit. A key over Γ's
   *content* would hit, at the price of hashing contexts.
2. Spell only what the export needs: the components of `pair@`, `fst@`,
   `snd@`, `inl@`, `inr@` in the *body*, and leave the binder domains'
   (types) to a translation that knows their whnf, which is item 1 of
   [[export-typed-translation]].
3. The typed exporter itself, which does the spelling's inference once, in
   the walk that translates.

Done when the sweep includes `ordered_field`, `rat` and `creal` inside the
rails.

## Resolution (2026-10-22)

Neither memo: the cost was not re-checking but a cascade. A
relation-parameterised class (no named record projections) projects its
fields with `fst@`/`snd@`; spelling one inlines the record's remaining Σ and
plants new `fst@`s in it, so each pass multiplies the next (Ring::neg_mul
grew per pass, ordered_field ran out of memory by the fourth). Both
targets type a projection from its pair (Lean `Expr.proj`, Rocq primitive
projections), so `⌊·⌋` for export now spells only the introductions
(`pair@`, `inl@`, `inr@`); `fst@`/`snd@` export as `Hx::Proj` (kernel route
line `j`), and `app@` as a plain application, as before. With that the sweep
has no left-out list: `ordered_field`, `rat` and `creal` export inside the
rails (design §5.6, §7). Item 1 of [[export-typed-translation]] is still
the route for the eta-long invariant, not for cost.
