---
title: A proper def: named values, not nullary fns
status: closed
labels: [frontend,syntax,language]
area: language
created: 2026-11-01
updated: 2026-11-01
---

A value definition, `def name: T = e;` (or `def name = e;` with `T`
inferred), as its own declaration form: a named constant that is not a
function of zero arguments. Today a constant is a nullary `fn` and is
used as `name()`.

The first customer is the DSL frontends of `docs/compilation-vision.md`
§3.3 and §6: `regex def is_hex = "[0-9a-f]+";`, where a language's
prefix generator receives the declaration, may rewrite its value (parse
the string into a term), and publishes the term, its meaning under the
declared name, and a `Compile` instance.

## Scope

- The form, its elaboration (same gate and image path as `fn`), use sites
  without `()`, and how it shows in diagnostics.
- Whether a `def` unfolds like a nullary `fn` today (it should, so
  closed verdicts by `refl` keep working).
- It takes generator prefixes ([[declaration-prefix-generators]]).

## Done when

`def` declarations elaborate and are used without `()`, a library constant
is migrated as an example, and a prefixed `def` reaches its generator.

## Log

- 2026-11-01: DONE (docs/metaprogramming/value-definitions-design.md §2). `def name<A>: T = e;` and `def name = e;` parse to a `DeclKind::Fn` with no written parameters and the new `Decl::value` flag, so a value is elaborated, gated, imaged and unfolded exactly as a nullary `fn` (closed verdicts by `refl` work through it; a nullary `fn` was already a global of type `T`, so `five` and `five()` both elaborated before). An omitted type is `TyKind::TypeOf(e)`, inferred once in `check_decl` (the value is the body); other readers of the stored declaration infer again. Use sites are bare; `five()` is refused across modules ("is a value (a `def`), not a function"), read off the registering layer. A value naming itself is refused as not recursive. Image: decl-kind tag 3 and surface-type tag 13, both new tags, so older images still decode; the round-trip unit test carries both. LSP lists a def as a constant; tree-sitter has `value_declaration`. Migrated example: `mono_carriers` (lib/std/tactic/mono.hthr). Probes: lib/_tests/std/core/value_definition_tests.hthr; parser refusals and the cross-module case: crates/elab/tests/value_definitions.rs. A prefixed `def` reaches its generator ([[declaration-prefix-generators]]).
