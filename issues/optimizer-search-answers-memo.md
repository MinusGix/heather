---
title: compile-x86 evaluates the optimizer's searches again over a warm store
status: open
labels: [native,compiler,performance,optimization]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-14
updated: 2026-11-14
---

`compile-x86`'s optimizer (`crates/cli/src/native/verified.rs`, `optimize`;
`docs/optimizer-design.md` §9.1) asks the library what to do a function and
a stage at a time: each question is an evaluation of a search
(`Function::find_inlined`, `find_guarded`, `find_learned_past`, …,
`Function::fits`, `Function::lowers`), read back as text. The store
remembers module images and the certificate's checked declarations, but not
a search's answer, so a compile over a warm store evaluates every search
again.

## Measured

2026-11-14, `scripts/bench-native` on the cloud box, after the optimizer's
step 4: `sha256_compress` over a warm store takes 76 s where it took 10
before the optimizer; `sha256_update` 78 s (12), `sha256_finish` 75 s (11),
`sha256_init` 22 s (4). The small exports (`sha256_t1`, `sha256_t2`,
`sha256_next`) are unchanged at about 2 s. The reads of a cold compile of
`sha256_compress` are 393 evaluations and about a hundred million evaluator
steps, the planner's (`Function::lowers`, and the placement read a second
time for the kept function) about two fifths of them.

## What to do

- **Remember a search's answer in the store**, keyed by the digests of the
  modules the probe imports and the expression read. This is safe without
  trusting the store: a search is not trusted, and the certificate states
  and checks what its answer made (`{prefix}_opt_made_{k}_{stage}`, by
  `refl`). A wrong or stale answer is a statement that does not check, never
  a wrong program. The yes/no reads (`fits`, `lowers`) decide only which
  candidate is kept, and a kept candidate the lowering refuses fails the
  compile loudly; they can be remembered the same way.
- **Read the placement once**: `Function::lowers` plans the function and
  the certificate's `plan_k` plans it again
  ([[compile-x86-address-space-margin]], "what is left").
- The address-space peak is the same issue's and is not helped by this.

## Built (2026-11-14)

`crates/cli/src/native/answers.rs`. Every read `compile-x86` makes on its
forks is remembered under `<cache-dir>/native-answers/`, one file an
answer: the optimizer's searches and its questions, the planner, the
emission, the layout and the bytes. The key is the binary's
`SemanticsIdentity` (elaborator and kernel sources), every source module
the session loaded by name and text (the bundled proof library and the
program's closure), every module the fork defined before the read in
order, and the name read. So a hit is a read whose whole world is the same
text; the generated texts carry everything the Rust side decides.

- **Written only after the certificate checks.** A read that went into a
  refused certificate is never remembered, so a stale answer cannot stick:
  the worst a wrong one can do is a refusal, and the next run evaluates.
- **Lazy probes.** A module the reads stand on is elaborated only when a
  read misses (`Reading::define`), with every module queued before it. A
  compile that hits throughout elaborates none of them, which was about a
  third of the warm time (the made functions are big literals).
- **The placement is read once.** The lowering's question now answers the
  placement it was asked with (`…_opt_placed`, generated beside the
  probes; `Function::lowers` in the library is no longer called), and
  that is the program's placement of a function the optimizer keeps. Only
  functions nothing reaches, or that the optimizer left alone, are planned
  by `…_plan_k`: 8 reads of 27 on `sha256_compress`.
- Answers no run has read for 14 days are removed when answers are saved.
  A hit renews its file's time. One compile of `sha256_compress` writes
  about 400 answers, 7.5 MB, against 83 MB of images in the same store.

Measured on the cloud box, release binary, `sha256_compress`:

| | wall | reads evaluated | evaluator steps in reads |
|---|---|---|---|
| warm store, before | 81 s | 418 | 119 M |
| warm images, no answers yet (first run of this build) | 73 s | 398 | 106 M |
| warm store with answers | 4.6 s | 0 | 0 (the shape read, 1.2 M, is before the optimizer and not remembered) |
| cold, before | 262 s | 418 | 119 M |
| cold, after | 261 s | 398 | 106 M |

The code and the certificate are byte for byte the same in every row.

The reads made before the optimizer (`runtime_shape`'s `…_shape`,
`runtime_entries`) are not remembered: they decide the program's shape and
the exported signature, outside `verified::compile`, and cost under a
second together. Whether every one of their answers is checked by the
certificate was not audited, so they were left as they were.

## Done when

A second `compile-x86` of `sha256_compress` over the store the first one
wrote is back near the time of a compile without the optimizer, and
`scripts/bench-native`'s warm column shows it.
