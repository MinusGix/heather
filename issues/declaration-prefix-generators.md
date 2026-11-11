---
title: Declaration-prefix generators: runtime fn f runs a library generator over f
status: closed
labels: [metaprogramming,syntax,elaboration]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-01
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

`runtime fn f` publishes `instance Compile(f)` in the R5d round, a test generator
prefix publishes a lemma about the function it prefixes, and the unknown and
non-generator prefixes are refused with their reasons.

## Log

- 2026-11-01: 2026-11-01: Widened (Minus, 2026-11-01, `docs/compilation-vision.md` §3.3, §6): a prefix generator may also REWRITE the declaration it prefixes, not only consume it elaborated. `regex def is_hex = "[0-9a-f]+";` gives the `regex` generator the declaration's syntax; it parses the string into a term and publishes the term, `is_hex` as the term's meaning, and `instance Compile(is_hex)`. So the mechanism has two modes: consume the elaborated declaration (`runtime fn`) and lower the declaration's syntax first (`regex def`), which is the distinction this issue's parent ([[scoped-declaration-generators]]) already draws. `def` itself is [[value-definitions]].
- 2026-11-01: DONE for the mechanism (docs/value-definitions-design.md §3); `runtime fn f` publishing `instance Compile(f)` is round R5d's ([[runtime-fn-default-setup]]), which owns the `runtime` generator. Built: `P decl` / `P(args) decl` over `fn`, `theorem` or `def` (one prefix; not over `axiom`/`meta fn`/`evidence theorem`; not in sections or under `assuming`, as `generate`). Calling convention: the declaration first, then the written arguments: `P("f", args)` for a consumed `fn`/`theorem` (published first; the generator `lookup`s it, since a `GlobalRef` is issued per run and none exists before it), `P("x", value, args)` for a rewritten `def` (not published as written; the group must declare `x`; a written type ascribes the value). One transaction: any failure publishes nothing, the prefixed declaration included. Unknown prefix: "`runtme` is not a generator in scope"; a non-generator is refused at its call with the convention spelled out. The generator's call is now kernel-checked before it runs (also for `generate`): elaboration defers some mismatches to the kernel, and a mismatched value used to reach the run as a stuck term. `DeclForm::AsValue` publishes a `def`. Customers: a test prefix publishing `f::at_zero: f(0) = …` about the `fn` it prefixes (lib/_tests/std/tactic/prefix_generator_tests.hthr, with every refusal), and `regex def is_hex = "[0-9a-f]+";` (lib/std/text/regex/regex.hthr; compiler half filed as [[regex-dfa-compiler]]).
