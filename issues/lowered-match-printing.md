---
title: Print a lowered match, convoy and if h: as the surface wrote them
status: closed
labels: [diagnostics, display, elaboration]
area: language
milestone: [lang-proof-modularity]
code: crates/elab/src/display.rs @ 7cda267
created: 2026-11-14
updated: 2026-11-14
---

A goal or hypothesis holding a lowered body printed as kernel syntax.
`let u = Sha256::begin_unfold(s, i); ?` showed

    u : begin(s, i) = app@(case[0,0,0](M Π[0,0](Id[0](El[0](u@83^{·}); …

and a mismatch involving an unfolding equation said its type "has no
surface spelling". Found while proving SHA-256's loops
(`/mnt/project-files/design/loop-proof-probe.hthr`, brief §5 of
`/mnt/project-files/design/language-feature-threads-2026-11-14.md`).

## What the display reads now

- **A case analysis over an enumeration** (a tier-0 inductive whose
  constructors carry nothing) is `match e { C₀ => …, … }`, read through the
  chain of cases a three-or-more constructor type lowers to; at the
  library's `Bool` it is `if e { … } else { … }`.
- **A convoy**, `case(z. Π(e = z). M; …)(refl)`, is `match h: e { … }` /
  `if h: e { … } else { … }`, the equation named `h` in each arm. This is
  what `match h:`, `if h:` and a `decreases` body's test lower to, so an
  unfolding equation now reads

      u : begin(s, i) = if h: unsigned_lt_bit(i, ofNat(8)) { begin(Sha256(s.hash, put(s.working, i, at(s.hash, i, inside := begin#found_2(i, h)), inside := begin#found_1(i, h)), s.schedule, s.count), i + ofNat(1)) } else { Mutated(s, i) }

- **A field read under a binder the walk crossed** (`s.hash` inside an
  arm) is typed where the walk stands (`Speller::here`) instead of
  declining. For a reader only: the source flavour still declines under a
  binder, as before.

Both new forms are for reading: the source flavour (`qualified`) never
takes them, so nothing that re-parses a spelling (omega's certificate)
sees them.

## Not covered

- A case analysis over a type whose constructors carry fields (`Option`,
  a payload variant): its arms read the payload through projections the
  display cannot name yet, so it falls back as before.
- A convoy over more than two constructors (its equation is threaded
  through the inner cases' motives).
- `unsigned_lt_bit(i, ofNat(8))` is how a `u64` comparison's bit and a
  `u64` numeral spell today; `i < 8` would need the operator table to
  know the bit, a separate change.

## Log

- 2026-11-14: built (thread "Fix inference and printing around match");
  probes `taken_wrong_arm`, `count_to_misread` and `turn_misread` in
  `lib/_tests/std/core/bool_tests.hthr` pin the
  messages through `expect-error`.
