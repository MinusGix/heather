---
title: Float and decimal literals, with a printer whose round trip is proved
status: closed
labels: [language,syntax,floating-point]
area: language
created: 2026-10-25
updated: 2026-10-26
---

Heather has no float literal and no decimal-fraction literal. Numerals are
the only `Rat`/`CReal` constants, and `docs/archive/radix-numerals-design.md` covers
only integers. Tests and clients build floats from fields. The Coq
hardware-float survey (`docs/coq-hardware-floats-survey.md` §5.3) sets out
the design Coq landed on, and the part Coq could not do that Heather can.

## Proposal

- **Exact hexadecimal float spelling** (`0x1.8p3`, `-0x1p-149`), extending
  the radix-numeral grammar. It denotes a `Dyadic`, and at a `Float(F)`
  expected type it is accepted only when representable. It is the
  information-preserving raw printing form.
- **Decimal spelling that rounds** (`0.1`, `1e-3`): it denotes the `Rat`,
  and at a `Float(F)` expected type it elaborates to `Format::round_rat`
  under `NearestEven`, the format taken from the expected type as for
  carrier-directed numerals. A warning appears when the value is inexact,
  decided by `round_rat_exact`.
- **A printer with a proved round trip.** Coq prints with `printf "%.17g"`
  and leaves an in-language printer as future work. Heather's printers are
  in-language already (`docs/parser-canonical-printers-design.md`), so
  the paper's Lemma 1 can be a theorem: for a format of precision `p`
  and output radix `β'` with `2^p < β'^(p'-1)`, printing `p'` significant
  digits and parsing by nearest rounding gives back the same float. Nine
  digits for binary32 and seventeen for binary64 are corollaries, and the
  shortest round-tripping output is a refinement.

Decimal literals at `Rat` (`0.5 : Rat`) fall out of the same grammar.
[[rat-numerals-and-semigroup-clash]] and [[all-numeral-relations-default-to-nat]]
show what defaulting such a literal must avoid.

## Done when

The lexer accepts both spellings, both elaborate at `Float(F)` and `Rat`,
the inexact warning fires and has a test, and the round-trip theorem is
proved for every `Format` (in `lib/std/num/float/`) for the printer that
renders floats.

## Log

- 2026-10-26: paused (Minus's call) until binary64 rounding evaluates in
  the kernel. Today `Format::round_rat` cannot: `Nat::pow(2, n)` meets the
  evaluator's depth budget past n ≈ 1024 ([[eval-native-frame-size]]), and
  `Nat::ldiv` on a 1000-bit numerator is exponential
  ([[kernel-fold-probe-evaluates-recursive-arms]]); details and the
  library-side fixes in [[nat-wide-evaluation]]. Work so far is on branch
  `claude/project-thread-vja39m`: `Nat::pow_sq` and the quotient-width
  `ldiv_fuel` with their specs (nat.hthr); four distance lemmas (rat.hthr);
  `lib/std/num/float/window.hthr`, which proves that a correct rounding in
  a window of `F` (same precision, `c + 1` binades from `emin + j`) read
  back in `F` is a correct rounding in `F`, for every format and mode
  (`Format::window_rounds`); and an unfinished
  `lib/std/num/float/literal.hthr`: `Format::round_scaled` (window placed
  by a binade estimate, checked conditions, `round_rat` fallback,
  overflow through `rounds_beyond`) evaluates 0.1, 1e300, max finite,
  1e400 → ∞, 5e-324 and 1e-400 at binary64 correctly, but its
  correctness proof is half written (`sc_pick_ok`, `sc_quot_ok` drafted;
  `sc_over_ok`, `sc_div_ok`, `round_scaled_correct`, exactness decision,
  lexer, elaboration, printer not started). The window algorithm is still
  the one to finish after the kernel fixes: it keeps every number about
  `prec + c` bits wide, which native compilation will want too.
- 2026-10-26: resumed after the kernel fixes (#185, #187) and landed the
  literals; `round_rat` still does not evaluate at binary64, so the window
  algorithm carries them. Lexer: decimal (`0.1`, `1e-3`, `2.5E+7`) and hex
  (`0x1.8p3`) spellings lex to `ScaledLit`. Elaboration goes through two
  classes in `rat.hthr`: `DecimalLiteral<A>` (`ofDecimal` plus an
  `exact` bit) and `HexLiteral<A>` (an `Ok` obligation the elaborator
  discharges with `trivial`), with instances at `Rat` and at every
  `Float(F)` (`lib/std/num/float/literal.hthr`). At a float,
  `Format::round_decimal` is proved correct for every format and mode
  (`round_scaled_correct`); `decimal_exact`/`hex_exact` reflect
  representability. An inexact decimal draws the `inexact-literal`
  warning (the bit is decided by the kernel); an inexact hex float is
  refused. Tests: `crates/elab/tests/lib_std_float.rs` (warning, hex
  refusal), `lib/_tests/std/num/float/literal_tests.hthr` (values at
  binary64/32 and e2m1, exactness bits, overflow, subnormals, Rat).
  Design: `docs/floating-point-design.md` §15. The printer and its
  round-trip theorem moved to [[float-printer-round-trip]]; closing.
