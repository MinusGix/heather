---
title: Normalise appends and other monoid terms instead of trans/cong_fn towers
status: open
labels: [tactics,proofs,stdlib,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-10-07
updated: 2026-10-07
---

Equations about appends are assembled by hand from `trans`, `cong_fn`, `sym`
and `List::append_assoc`. The library has about 1,175 `trans(`, 714 `j(` and
416 `cong_fn` uses; `elf64_command_output.hthr:192-200` is a typical tower.
`Monoid<List<A>>(append)` already exists (`lib/std/algebra/algebra.hthr:178`), and
nothing in the native library uses it.

Wanted:

- A normaliser keyed on any `Monoid` instance (an `ac_rfl` for one
  associative operation with unit): it closes goals equal up to
  reassociation and unit laws, and emits an ordinary proof term.
- Homomorphisms as a class (`MonoidHom`), so the normaliser pushes
  `filter_emitted`, `sent_to(fd, ·)`, `len` and similar through appends;
  today that is `filter_emitted_append` plus `append_assoc` by hand.
- Commutative instances (`Nat` addition, `BitVec` addition for the totals)
  as a later step.

## What it assumes from elsewhere

- **[[tactic-composition-ergonomics]]** owns how a normaliser composes with
  `split_all`, `omega` and alternation.
