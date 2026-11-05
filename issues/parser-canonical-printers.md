---
title: Pair parsers with canonical printers and checked round trips
status: open
labels: [stdlib,parsing,proofs]
area: heather-in-heather
created: 2026-09-15
updated: 2026-09-15
---

## Problem

A parser may admit many spellings of one value or discard information through mapping. Some parsers can still support a canonical reverse direction: generate tokens which that exact parser reads back as the supplied value.

## Scope and acceptance

Design an optional operation-indexed class, provisionally Prints(p), carrying print: A -> List<T> and a whole-input round-trip law for complete(p). A restricted variant takes Printable(a) evidence. Allow explicit dictionaries or an indexed printing policy: one parser can have several useful canonical renderings, so instance uniqueness must not accidentally choose formatting. If equality is too strong for normalized or proof-bearing values, specify an explicit observation/equivalence and require its laws.

Composition needs an explicit boundary contract. Do not assume parsing print(a) ++ tail leaves tail unchanged: greedy recognizers can absorb suffix tokens. Investigate permitted suffix predicates, delimiter/framing guarantees, and exact consumed-offset laws.

For map(f), require a section choose: B -> A with f(choose(b)) = b, optionally restricted to representable B; injectivity of f is unnecessary. For bindD, print the first component then its indexed payload. Ordered choice also needs branch compatibility: an earlier branch may intercept the chosen branch output. Repetition needs separation/boundary evidence as well as consumption.

Prototype token selection, framed sequencing, a many-to-one mapping with canonical choice, and a dependent length-prefixed format. Include negative controls for a wrong printer, a false map section, greedy suffix absorption, and ordered-choice interference. Explain both laws separately: parse(print(a)) recovers a; print(parse(tokens)) may normalize tokens and need not recover their original spelling.

Acceptance: a checked open round-trip theorem, no unchecked axiom, explicit support limits, and an ergonomic demonstration. Grammar soundness alone does not establish printer round trips: generation must be connected to recognition.

## What it assumes from elsewhere

[[parser-grammar-soundness]] owns independent recognition soundness; [[parser-dependent-format-client]] supplies a dependent-format example; [[parser-certificate-ergonomics]] owns generic certificate ergonomics.

## Design notes

See `docs/parser-canonical-printers-design.md` for the proposed contracts, including source-context dependence and boundary counterexamples. This remains design work, not an implemented printer API.

## Log

- 2026-11-05: gardener: cites a file it shares with [[float-printer-round-trip]] (`docs/parser-canonical-printers-design.md`).
