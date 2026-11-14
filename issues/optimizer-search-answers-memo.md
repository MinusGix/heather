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

## Done when

A second `compile-x86` of `sha256_compress` over the store the first one
wrote is back near the time of a compile without the optimizer, and
`scripts/bench-native`'s warm column shows it.
