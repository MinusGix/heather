---
title: A proper def: named values, not nullary fns
status: open
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
