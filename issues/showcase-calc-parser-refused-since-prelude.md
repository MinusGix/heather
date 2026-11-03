---
title: calc_parser showcase is refused from scratch since the common prelude (#406)
status: open
labels: [regression,elaboration,literals]
area: language
created: 2026-11-03
updated: 2026-11-03
---

`heather check -L lib/std -L lib/std/parser docs/showcase/calc_parser.hthr`
(the showcase's own search path, `docs/showcase/showcases.tsv`) refuses the
showcase with 36 errors since #406 (9ba4a590, the common prelude and literal
classes read by identity); f8f129a5 just before it checks. Bisected
2026-11-03 by building each merge over its own tree.

The first refusals are `Grammar(0)` / `Grammar(1)` (calc_parser.hthr:285,
288): `no instance for Numeral<Derivation>`. `Grammar` is a record whose
first parameter is `level: Nat`, and the call is the type former partially
applied; the numeral is now read at the constructor's first field
(`derivation: Derivation`), so the bare name seems to resolve to the
constructor where it used to resolve to the type former (or the numeral's
Nat fallback no longer applies when `Numeral` is reached by import). The
other 33 errors are the cascade (`parse`, `execute`, … unbound).

**Why the suite is green:** `crates/elab/tests/showcase_calculator.rs` and
`crates/cli/tests/showcase.rs` run over replayed module images, and the
showcase is not under `lib/`, so `heather check -L lib --expectations lib`
does not see it either. `scripts/perf ab`'s default corpus (calc_parser)
fails on both sides, which is how it was found.

## Done when

The showcase checks from scratch again, and something that re-elaborates
the showcases (the nightly exact-image lane, or a fresh `--pr` run when
`crates/elab` changes) would have caught it.
