---
title: No existential/Σ at the statement level
status: open
labels: [frontend,elaboration,design]
created: 2026-07-31
updated: 2026-08-01
---

Filed out of the [[ir-simulate-design]] fuel-interface round, which wanted
`converges(p, f, args, vs) := exists n. simulate(p, f, args, n) == Out(vs)`
(design doc section 6) and could not state it.

What is missing, precisely: a **dependent pair whose second component's type
depends on a value the surface supplies**, usable as a *predicate*. Today:

- `record` has dependent fields, but only **type** parameters (`record R<A>`),
  so a record cannot be indexed by `(prog, env, ir, vs)`. An un-indexed Σ over
  all of them is a different proposition — it is inhabited by any converging
  program, so it proves nothing about a particular one.
- Declaring an indexed inductive family has no surface syntax at all
  ([[indexed-families]]; the prototypes in `crates/elab/tests/indexed_route1.rs`
  and `indexed_declared_index.rs` are hand-built kernel terms).
- A `fn` returning `Type<0>` cannot help: a `fn` body is an *expression*, and
  the expression grammar has no `->` (the motive path now parses its body with
  the type grammar, but that is one position, not the general case —
  [[type-definitions]] owns closing it).

The workaround in use, and it is a good one for its consumer: the
**computed-bound** form. `converges` becomes `eval(bound(args), p)(env, ir) =
Out(vs)`, and `refines` carries a fuel map instead of an existential
(`refines_trans` is then composition of the maps). Recorded as note 7 of
`docs/ir-simulate-design.md`. The ∃-form is the image of the bounded form
under the ∃-closure, so nothing there has to be re-proved when this lands.

Two candidate routes, neither costed:

1. **Value parameters on `record`/`inductive`** — `record Ex(p: Prog, env: Val)
   { … }`. This is the small version and it is what the consumer wants.
2. **A general Σ**, which needs a type-family-valued parameter (`B: A ->
   Type<0>`) and so wants the second component's type to be an *applied*
   expression in type position. Bigger; overlaps [[surface-polymorphism]].

## Log

- 2026-08-01: A second customer class, from re-reading the landed round:
  **inversion lemmas**. `step_mono`'s remember-idiom chains (four of them)
  each re-derive by hand what one reusable lemma would give —
  `k_bind(ev, env, rest, r) = Out(vs) -> exists ws. (r = Out(ws)) × …` —
  and that statement is exactly a value-indexed Σ. Until this lands, every
  proof that scrutinizes a sub-region's `Res` re-plays the case analysis
  inline; [[match-with-equation]] owns making the inline form less scary,
  this issue owns making it unnecessary. Priority datum, not scope change.

- 2026-08-01: **Route choice settled by investigation: route 1, and it is
  cheaper than the issue assumed.** Report:
  `docs/surface-existential-investigation.md`. Verdict: value parameters on
  `record` need **no kernel change, no new former, no ch. 07 obligation**,
  and **none of [[indexed-families]]'s machinery** — the parameters-not-
  indices claim is confirmed against the tree, and the classifier's own
  message (`inductive.rs:1511-1519`, which pushes a uniform bare-variable
  index toward fording) is the thing the round has to correct. Two
  prototypes, both green: `crates/elab/tests/surface_existential_probe.rs`
  (9 tests, hand-built kernel terms — `Σ n. dbl n = m` at an **open**
  parameter forms, is introduced on fully open data, is *eliminated* by
  instantiating an open type family at the witness and transporting along
  the equation with `J`, has Σ-η at a neutral pair, and rejects a witness
  for a different parameter); and, at the surface, the **real** `Converges`
  over `lib/ir_v1.hthr`'s `eval`/`Prog`/`Ir`/`Val`/`Res` at concrete
  arguments — it declares, is introduced by a computed bound with the
  equation closed by conversion, and its projections feed `fuel_monotone`.
  So everything except *writing the parameters as parameters* already works.
  Dependent fields with a **computed** type (`record Small { n: Nat, h:
  leb(n)(5) = True }`) already work too, so that gap is not on the bill.
  Gap list: parser (small — `record R(p: T)` is a clean parse-error position
  today and `fn` shares no grammar), AST params split (small, wide),
  substitution into field types (small — `TyVar`/`Alias`'s `depth` +
  `shift_local` verbatim), use-site formation (small — `Converges(a,b,c,d)`
  in type position already parses and already reaches `try_indexed_ty`),
  construction (**medium**, the only real design decision: checking position
  supplies the parameters), projection/match (small). Route 2 deferred: type
  arguments are `Ty`s and no `Ty` denotes a family, plus parameters are
  monomorphized by design — a different round, overlapping
  [[surface-polymorphism]]/[[type-definitions]]. One stated risk: an
  un-shifted parameter under the Σ binder is a **well-formed but wrong**
  proposition the kernel cannot catch, so the acceptance suite needs a
  negative control on the proposition, not only on the encoding.

## What it assumes from elsewhere
- **[[indexed-families]]** owns whether declared families come from indexed W
  or ford over `Wf`. Assumed here: only that the surface has no syntax for
  declaring one today.
