---
title: Mutual recursion: declaration groups and a shared termination argument
status: open
labels: [frontend,elaboration,design]
created: 2026-09-05
updated: 2026-09-05
---

Filed off the [[termination-measures]] round (2026-09-05), which landed
`decreases` for a single declaration and deliberately not this. The showcase
parser (docs/showcase/idealized.hthr: `parse_expr` / `parse_factor` /
`parse_atom`, all `decreases ts.len()`) is the customer.

What it needs, in order:

1. **A declaration group.** Today every `fn`/`theorem` is elaborated and
   registered alone, and a name is not in scope until its declaration is
   checked (`Cx.selfref` is the one exception). A group needs the members'
   *signatures* registered before any body, and their bodies checked against
   a shared recursion.
2. **One recursion for the group.** Under a measure the natural lowering is
   the single-declaration one (docs/termination-measures-design.md §2) over a
   *sum* of the members' parameter telescopes: `F(n, which, x̄)` by strong
   induction on the bound, with each member a projection. Structural mutual
   recursion (`even`/`odd`) is the same over a sum of the descending
   arguments, but the eliminator does not hand out a sibling's ih, so the
   measure route is the one that generalizes.
3. **Obligations across members.** A call from `parse_expr` to
   `parse_factor` owes `measure_factor(ȳ) < measure_expr(x̄)`, stated with
   each member's own measure; the refinement convoy (design §3) is per body
   and composes.

Not a small round. The showcase row stays on this issue.

## What it assumes from elsewhere
- **[[termination-measures]]** owns the single-declaration measure. Assumed
  here: only the lowering shape, so that a group can be one instance of it.
