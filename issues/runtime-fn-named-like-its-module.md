---
title: A runtime fn named like its module cannot publish its members
status: open
labels: [native,metaprogramming,elaboration]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-04
updated: 2026-11-04
---

`runtime fn mix` in `mix.hthr` is refused: "the generated `mix::rt` was
refused: `mix::rt` would read as `rt` in the module `mix`, not as a member
of the function `mix`". The same holds for `program` in `program.hthr`. The
round that put the examples through `Compile(f)` renamed the files
(`word_mix.hthr`, `levels.hthr`, docs/runtime-fn-setups-design.md §16.9)
instead.

The check guards a real ambiguity in how `a::b` is read. Any generator
that publishes `f::…` members (`runtime`, `regex def`) meets it whenever a
module exports a function of its own name, which is the natural way to
write a one-function file.

## Scope

Decide how `m::f::x` and `f::x` read when `f` is both a module and a
function of it (the function's member wins inside the module, the module's
binding outside, or qualified-only), and let the generated group publish.

## Acceptance

- `runtime fn mix` checks in `mix.hthr`, and `compile-x86 mix.hthr mix`
  compiles it.
