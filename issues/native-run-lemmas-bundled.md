---
title: "Run lemmas over a structure, and Region::paired without written matches"
status: open
thread: Make compiler correctness proofs elegant
labels: [native,proofs,itree,ergonomics]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-17
updated: 2026-11-17
---

The proof side of `docs/library/program-and-proof-style.md` §3, in
`lib/native/native_compile_correct.hthr`:

- `Region::paired` is seven written motives in fifty lines, matches on
  `reads_known()` and `leaves_known()` restated in each motive.
- `Target::goes_repeat` takes some twenty parameters (the body, its code,
  three `Within` facts, the live sets, the continuation and its two
  obligations), and `Stmt::emits_runs`'s `Branch` arm writes
  `ITree::bind(Events::linux(), match env.bit(condition) as λ _ => … {
  True => yes.denote(…), False => no.denote(…) }, k)` three times.
- `Target::procedures_body` and `native_compile_correct_bare` open with a
  seventeen-binder λ and thirty `let`s of positions.

## Wanted

- The continuation with its obligations (`k`, `exits`, `next`) as one
  value the run lemmas take, and the emitted piece with its `Within` fact
  as one value ([[emitted-code-claims-without-positions]] may remove the
  second altogether).
- A name, or a surface form, for "the tree of a statement followed by `k`"
  and for a branch on a bit of the environment, so a proof says it once.
- `Region::paired` by `cases` or `match h:` once its statement stops
  restating `Stmt::pair_known`.

## Done when

`Target::goes_repeat` takes under ten parameters and `Region::paired` has
no written motive.

## Log

- 2026-11-17: filed from Minus's review of `lib/native/native_compile*.hthr` (`docs/library/program-and-proof-style.md`).
