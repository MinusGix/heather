---
title: "Emission takes its checks' proofs and returns code, not an Option of it"
status: open
thread: Make compiler correctness proofs elegant
labels: [native,design,proofs]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-17
updated: 2026-11-17
---

`Stmt::emits` returns `Option<Compiled>`, and it is `None` only where a
check fails: `layout.word_fits`, `layout.words_fit`, a capacity looked up
(`layout.capacities.nth(buf)`), `region.scopes()`, `layout.call_fits`. Every
theorem about emitted code therefore starts from `emitted: s.emits(…) =
Some(c)` and inverts it stage by stage, and where a stage has no name the
hypothesis restates the callee:

```
emitted: (match region.scopes() { False => None, True => region.code(p, layout, out, names) }) = Some(c)
```

The inversions were most of the written motives in
`native_compile_correct.hthr`. `cases h` automates them
([[cases-on-hypothesis-tactic]]); this issue is about not having them.

## Wanted

One check of a statement against a layout (`s.fits(layout)`, a `Bool`, or
the conjunction of the checks above with named parts), and emitters that
take its proof and return code. A partial operation takes a found proof
(`docs/library/program-and-proof-style.md` §1). The compile's entry point
tests the check once and is the only `Option`.

To settle: whether the proof is a parameter, a `When`, or a field of the
context ([[native-emission-context]]); how a lookup's result (`capacity`)
reaches the emitter without a second lookup; what `write-elf`'s
stage-at-a-time converses (`Stmt::emits_then_of` and the rest) become, as
they exist to state a long emission in pieces.

## Done when

No theorem in `lib/native/native_compile_correct.hthr` takes a hypothesis
of the form `… = Some(c)` about emission, other than the one about the
whole compile.

## Log

- 2026-11-17: filed from Minus's review of `lib/native/native_compile*.hthr` (`docs/library/program-and-proof-style.md`).
