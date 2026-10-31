---
title: Declaration-prefix generators: runtime fn f runs a library generator over f
status: open
labels: [metaprogramming,syntax,elaboration]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Slice R5c of `docs/runtime-fn-setups-design.md` (§9.1): a declaration
prefix that names a generator, the first syntax-carrying form of
[[scoped-declaration-generators]].

## Scope

- An item `IDENT fn …` or `IDENT(args) fn …`: the `fn` is elaborated and
  published as written, then the generator `IDENT` resolves to (an ordinary
  library function returning `Tac<List<Decl>>`, taking the new function's
  `GlobalRef` and `args`) runs, and its group is published beside it, or the
  whole item is refused with the generator's error.
- Modifier keywords (`meta fn`) are matched first. An unknown prefix is
  refused by name ("`runtme` is not a generator in scope").
- The generator's group may cite the declaration it prefixes.

## Done when

`runtime fn f` publishes `f::runtime` in the R5d round, a test generator
prefix publishes a lemma about the function it prefixes, and the unknown and
non-generator prefixes are refused with their reasons.
