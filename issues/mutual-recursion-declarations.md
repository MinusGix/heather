---
title: Mutual recursion: declaration groups and a shared termination argument
status: closed
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

## Log

- 2026-09-05: Chartered (user, 2026-09-05) as Part B of the same managed round as [[decreases-unfolding-equations]], after it lands. Open design question the charter names: the idealized parser writes NO group keyword (three adjacent declarations), so adjacency-inferred groups vs an explicit block is the first thing the design pass settles.
- 2026-09-05: Design pass accepted (2026-09-05, docs/mutual-recursion-design.md). Verdicts binding on the implementing pass: groups are inferred from ADJACENCY (a run of consecutive decreases-declarations, SCCs under the syntactic call graph), no keyword, no AST/image change; the recursion's motive is the PRODUCT of the members' motives (nested pair::Pair), not the issue's sum of telescopes — no common telescope or result type required; the same-measure sibling call (parse_expr -> parse_factor on the same ts) is paid by a lexicographic measure flattened to e*N + rank, rank = declaration order first-declared highest, omega closing the arithmetic; the issue's item 1 (signatures before bodies) dissolves since every sibling call is rewritten to an ih projection before elaboration. Deferred as residue: structural even/odd with no written measure (measure synthesis), and unfolding companions for a group. Surfaced and filed: [[omega-measure-at-constructor-pattern]], [[omega-renders-member-by-base-name]] — both stand between the customer and omega-only obligations.
- 2026-09-05: LANDED (2026-09-05, managed round; docs/mutual-recursion-design.md, §12 for what implementing corrected). Adjacency-inferred SCC groups over runs of decreases-declarations; product motive over nested pair::Pair; lexicographic measure flattened to e*N + rank; the both-sides refinement of the obligation transport (free for singletons). The showcase parser's three members group, check and compute; the gap-table row is rewritten. Rider: half of [[omega-renders-member-by-base-name]] fixed (qualified atoms; unspellable hypotheses skipped). Residue: [[group-unfolding-equations]], [[mutual-recursion-measure-synthesis]]; the customer's idealized spelling still waits on [[omega-measure-at-constructor-pattern]] and Result/?. Suite 2414 -> 2426 (coordinator: full run INCOMPLETE under load, the three decreases targets rerun standalone green, 0 failed).
