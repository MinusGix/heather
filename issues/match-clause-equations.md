---
title: Nested patterns give each clause its full equation
status: open
labels: [elaboration,match,patterns,proofs]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 5 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §7). Needs [[match-equation-in-every-arm]] and [[match-refines-computed-scrutinee]].

`prepare_arms` compiles deep patterns to nested matches on column variables. The outer equation mentions the columns, so refining it at each inner level (slice 2's rule over pending equations) makes it `s = C(x, D(y, t))` at the leaf, with no composition proof.

## Done when
- Probe P4 checks (design §12.1), which closes [[eqbind-deep-pattern-kernel-rejects]].
- [[deep-pattern-dependent-later-field]] is checked here.
