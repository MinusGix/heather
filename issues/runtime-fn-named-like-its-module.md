---
title: A runtime fn named like its module cannot publish its members
status: open
labels: [native,metaprogramming,elaboration]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-04
updated: 2026-11-12
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

## Log

- 2026-11-12: Met again writing SHA-256's compress (2026-11-12): a `runtime fn sha256_compress` in `sha256_compress.hthr`, and one function `sha256_round` in a module that imported `sha256_round.hthr`. Two things worth keeping. The refusal is the generator's last step, so it shows only once everything before it passes: here that was after a day spent on [[runtime-link-compares-functions]], with the name clash waiting behind it; a check of the function's name against the modules in scope at the head of the generator would say it first. And the clash is with any module in scope of that name, not only the function's own file. The module is `sha256_block.hthr` and the round `sha256_step` for this reason.
