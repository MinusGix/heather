---
title: Every conversion query builds Γ's identity environment, so a match k cases deep pays Θ(k) per query
status: open
labels: [kernel,performance,inductives]
area: kernel
code: crates/kernel/src/conv.rs:624 @ 3e23503
created: 2026-10-26
updated: 2026-10-26
---

Found by `inductive/isa-roundtrip` after
[[wide-inductive-constructor-mention-cost]] took the constructor values out
of it: what is left of the roundtrip is the identity theorem, `match i {
Iₖ(a, b) => refl, … }` over an `n`-form type, and its gate grows faster than
its counters. From 128 to 256 forms (release, width one, cloud box) every
kernel counter of `ident_id` grows about 4× (eval steps, conversion misses,
`local_subst_nodes`, `global_ref_rescopes`) — the quadratic the right-nested
encoding implies, arm `k` sitting under `k` case layers — while the gate's
time grows about 7×.

gdb stack samples during that gate (three of three that landed in the
kernel) sit in `value::Env::identity`, under `conv::Env::new_with` ←
`conv_type_cached` ← `Tc::conv_ty`. `value_scope` builds the identity
environment of the whole Γ, one arena node per entry, at the root of
**every** conversion query (`crates/kernel/src/conv.rs:624`). Under a
`match` arm `k` cases deep Γ has `k` more entries, so each of the arm's
queries pays Θ(k) before it compares anything, and the declaration pays
Θ(n) per query on top of the Θ(n²) query count.

## What a fix looks like

The identity spine is the same for every query over the same Γ (it is
`Env::identity`'s doc: every identity environment is a prefix of every longer
one), so it does not need to be rebuilt per query; but it lives in the
query's arena, and an arena that outlives a query is the thing
`docs/intro-by-type-design.md` §3.7 prices separately. Two directions:

- An environment whose tail *is* the identity without being materialized:
  a length `base` below which `lookup(i)` answers `Val::var(level)` directly
  (the way `Lookup::Base` already answers past the end). `Env::ptr_eq` and
  `values_ptr_eq_prefix` must keep treating two identity tails of the same
  length as identical; [[env-lookup-depth]] is redesigning the same
  structure and owns that representation.
- Build the spine lazily, up to the deepest variable a query actually
  forces.

Acceptance: `ident_id`'s gate grows with its counters (about 4× per doubling
on `inductive/isa-roundtrip`), measured with `scripts/perf ab`.

## What it assumes from elsewhere

- **[[env-lookup-depth]]** owns `value::Env`'s representation. Assumed here:
  only that a query's root environment is still the materialized identity
  spine.

## Log

- 2026-11-05: gardener: cites a file it shares with [[conversion-typed-eliminator-congruence]] (`crates/kernel/src/conv.rs`); [[indexed-families]] (`crates/kernel/src/conv.rs`).
