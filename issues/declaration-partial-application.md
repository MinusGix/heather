---
title: A declaration applied to some of its arguments is refused
status: closed
labels: [elaboration, ergonomics]
area: language
created: 2026-11-09
updated: 2026-11-09
---

`List::LexAt(R)` for `fn List::LexAt<A>(R, xs, ys) → Type` is refused
("`List::LexAt` is applied to too few arguments",
`crates/elab/src/application.rs`), so a relation-valued declaration that
classes want unapplied in its last arguments (`LinearOrder<List<A>>(…)`,
`xs.Sorted(…)`) needs a second declaration that is a λ over them:
`lib/std/data/sorting.hthr`'s `List::Lex(R) = λ xs ys => LexAt(R, xs, ys)`.
A wholly unapplied name works (`Nat::Le`, `RelId<Nat>`); only the partial
case is missing.

## Done when

A call with fewer explicit arguments than the declaration takes elaborates
to the η-expansion over the rest (at least at a checking position whose
expected type is a function type), and `List::Lex` can be `LexAt` itself.

## Log

- 2026-11-09: Done. The implicit-inserting application stops when it runs out of arguments with only explicit, default-free, solver-free parameters left, and returns the call as the function of the rest (η-short), wherever a function is wanted: inference, or a stated result that is a Π (crates/elab/src/application.rs). A stated result of another type keeps the arity error. `List::LexAt` is now `List::Lex` itself, applied to `R` alone where a relation is wanted; probes in lib/_tests/lang/partial_application_tests.hthr.
