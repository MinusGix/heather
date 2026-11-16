---
title: Subscript-decorated relation symbols and rounding notation
status: open
labels: [syntax,notation,floating-point]
area: language
milestone: [math-float]
created: 2026-10-20
updated: 2026-10-20
---

The float library (`docs/library/floating-point-design.md` §4.2, §5.5; milestone
`math-float`) wants notation the lexicon does not have. Asking for one
general rule plus a few tokens is better than adding one-off tokens:

1. **Subscript-decorated relations.** A relation symbol (`<`, `≤`, `=`,
   `≈`) immediately followed by one Unicode subscript letter
   (`ₐ ₑ ₒ ₓ ₕ ₖ ₗ ₘ ₙ ₚ ₛ ₜ ᵢ ⱼ ᵣ ᵤ ᵥ`) lexes as one symbol, a name in the
   symbol namespace given meaning by `designation` like `<`
   (`docs/language/classes/operators-onto-classes-design.md`). This is the same adjacency
   rule `·₁₂` already uses. Floats use `<ᵢ ≤ᵢ =ᵢ` for IEEE quiet comparison
   and `<ₜ ≤ₜ` for totalOrder. Other uses: `≤ₗ` lexicographic, `≈ₛ` a
   second setoid.
2. **`≤` as a Unicode spelling of `<=`** (and `≥` of `>=` if that exists),
   needed for `≤ᵢ` to read naturally.
3. **Rounding tokens.** Prefix `○`, `▽` and `△` (with `○[mode]` and `○ᶠ`),
   and infix `∈` for "is a member of the set of roundings". `∈` has uses
   well beyond floats (finite sets, `Within`).

Constraints: parsing stays context-free (`issues/notation-extensibility.md`).
The decoration is lexical, and meaning comes only from designations.

The float rounds do not wait on this. They use named functions (`ieee_lt`,
`total_le`, `RoundsTo`, `round`), and the notation becomes designations
over them with no change to any theorem.
