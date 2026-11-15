---
title: Termination beyond structural: decreases clauses, consumption postconditions
status: closed
labels: [frontend,elaboration,design]
created: 2026-08-13
updated: 2026-09-05
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

## Log

- 2026-09-05: LANDED layer 1 and the lemma route of layer 2 (docs/language/recursion/termination-measures-design.md): `fn f(x̄) -> T decreases e { … }` elaborates by a surface desugaring to strong induction on the bound Succ(e) — a written-motive match with the explicit-ih arm, parameters re-bound under their own names, each self-call f(ȳ) rewritten to ih(ȳ, le_trans(Succ(e[ȳ]), e, k, obligation, h)). Obligations are goal holes ?decN (source order), discharged by `on ?decN := …` or by omega where omega and int are imported. A match on a variable the measure mentions is convoyed through a hidden equation binding so the obligation is stated at the pattern (mod(a, Succ(k)) < Succ(k), not < b) and transported back by j. Omega now reflects an open Succ(t) as t + 1. Customers: gcd (lemma), merge (two on's), a callee-postcondition descent (the parser shape, lemma route), theorem-by-measure (omega). Residue with owners: [[mutual-recursion-declarations]] (the showcase's three parsers), [[decreases-unfolding-equations]] (open-argument unfolding for proofs about a decreases-defined function); the refined-return route is not built — a refined return is a record whose proof field is the lemma. No kernel change. Acceptance: crates/elab/tests/termination_measures.rs.
