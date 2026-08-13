---
title: Termination beyond structural: decreases clauses, consumption postconditions
status: open
labels: [frontend,elaboration,design]
created: 2026-08-13
updated: 2026-08-13
---

Filed off the showcase critique (2026-08-13, docs/showcase/README.md gap
table row "decreases"). The idealized parser
(docs/showcase/idealized.hthr) is the canonical customer:

    fn parse_expr(ts: List<PTok>) -> Result<(Expr, List<PTok>), ParseError>
        decreases ts.len()

Three layers, in ascending order of design content:

1. **A measure annotation** (`decreases <expr>`) for recursion the
   structural checker declines — mutual recursion included (`parse_expr` /
   `parse_factor` / `parse_atom`).
2. **The measure alone is not enough** for the parser shape: the recursive
   call is on a suffix *returned by a callee*, so the decrease rests on the
   callee's postcondition ("parse_factor's returned suffix is strictly
   shorter when it consumed"). Somewhere that fact must flow: Lean-style
   separate lemmas the checker consumes, or intrinsically in the return
   type — `{rest: List<PTok> | rest.len() < ts.len()}` (Agda's total
   parser combinators, matured). Discussion leaning (2026-08-13): the
   refined-return-type spelling is troublesome but natural in some cases
   and "might make a lot of inference tricks easier" — both routes stay on
   the table.
3. The loopification/certgen interaction is NOT this issue: kernel-side
   termination is by construction (eliminators); this is purely the surface
   checker's vocabulary for justifying elaboration into them.

Adjacent: [[ih-generalization]] (varying non-decreasing arguments is the
sibling gap and shares the checker), [[match-recursion]] (the structural
slice, closed).
