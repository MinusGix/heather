---
title: calc_parser showcase is refused from scratch since the common prelude (#406)
status: closed
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

## Log

- 2026-11-03: Fixed: the numeral was read at the constructor because common's export of `Numeral` made every module name the class, so a failed `Numeral<Derivation>` search inside the speculative constructor reading of `Grammar(0)` was a hard Resolution error rather than the Nat fallback that lets the family reading win. A class named only through the common prelude (`Names::seen_only_through`) now keeps the fallback (`literal_class_record`, traits.rs); a module importing the class itself still gets the error. Probe: `tagged_family` in lib/_tests/std/core/common_tests.hthr (refused on master). Every in-process showcase row now also has a `cli_check_<name>` test in crates/cli/tests/showcase.rs, which runs through the loader and so sees the implicit prelude; `in_process_rows_each_have_a_cli_test` keeps that list equal to the manifest's in-process tiers.
