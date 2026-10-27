---
title: Each member of a mutual group re-judges the family signature in its own statement gate
status: open
labels: [elaboration,inductives,performance]
created: 2026-10-27
updated: 2026-10-27
area: language
milestone: [math-metatheory]
---

Left by [[iwf-shape-spine-comb-depth]] once the recursion's own gate became
about linear in the members. Measured 2026-10-27 on the `mutual_group` ring
with one `sizeᵢ` per member (`heather check --timings`, release, width one,
cloud box, whole file; a per-gate probe around `typing::check_type` /
`check_term`), what is left superlinear is outside the recursion:

1. **Each member's statement re-judges the family's signature.** The group
   generates one wrapper per member, `sizeₜ(t: Mₜ) -> Nat`, and each is its
   own declaration, so its statement gets a fresh checker. `Mₜ` is
   `IWf(I; S; …)(Dₜ#member)` with the index type `I` (the member sum) and
   the shape `S` spelled inline, Θ(m) each, and the checker judges both
   (`Tc::iwf_sig_premises`): Θ(m) per wrapper, m wrappers. At m = 160 the
   160 statement gates were about two thirds of the group's gate. Neither
   signature memo can help across gates (they live for one gate), and
   within one the named signature's `D#iarity`-style references carry
   `·^|Γ|` tails, so `Tc::closed_sigs` declines every occurrence
   (`bounds::iwf_sig_locally_closed`).
2. **Elaboration lowers the shape at every mention.** `Elaborator::iwf_sig`
   calls `lower_shape` (Θ(m)) per mention of the family, and
   `share_iwf_part`'s guard is a Θ(m) `==` against the kept copy; every
   wrapper and every constructor value mentions the family.
3. **Global shifts walk global-free subtrees.** `ShiftGlobal` has no skip, so
   rescoping a named-signature definition's type into a gate's Ψ walks its
   Θ(m) shape domain (the `rescope` column is quadratic over the ring) though
   nothing in it changes; the node is shared afterwards, only the walk is
   paid.

Directions, not yet weighed against each other: spell the member types by
reference in statements (a registered code for each member, or the shape and
index type named in the signature beside `D#iarity`, so a statement gate
judges references), which removes 1 and most of 2; a global-use bound in
`bounds.rs` that lets the global mappers skip, which removes 3 everywhere.

Acceptance: `inductive/mutual-recursion` towards 1 over 4..32 and the ring's
whole-file gate about linear from 80 to 160, or a recorded reason.
