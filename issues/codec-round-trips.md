---
title: Codecs as partial isomorphisms with round-trip combinators
status: open
labels: [encoding,native,x86]
area: mathematics
milestone: [none]
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/arch/x86_64/x86_64.hthr` proves a decoder round-trip per
instruction form (`decode_instruction_of_rr_encoding`, `_mov_ri_`,
`_setcc_`, `immediate_bytes_roundtrip`, `gpr_fields_roundtrip`); utf8, ELF
and the decimal reader repeat the pattern. `docs/surveys/native-mathematics-survey.md`
§8; survey rank 9.

## Scope

- A codec as an encoder and a decoder of a prefix, with round-trip
  (`decode(encode(a) ++ rest) = Some(a, rest)`) and, where it holds,
  canonicity.
- Combinators proved once each: fixed-width little-endian fields, bit
  fields, sequencing, choice by a tag (Rendel and Ostermann, invertible
  syntax descriptions; Narcissus, ICFP 2019).

## Done when

One instruction form's round-trip is a composition of combinator lemmas,
and the next instruction added to the encoder costs no new round-trip
induction.
