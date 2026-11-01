---
title: A chain of nested matches on ∃ results is superlinear in elaboration and in the kernel
status: open
labels: [elaboration,performance,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-10-31
updated: 2026-10-31
---

The product rule of the uniform derivative (`DerivOn::mul`,
`lib/std/analysis/real_fn.hthr`) picks eleven moduli in sequence, each from
an `∃` that the previous ones feed. Written as eleven nested
`match … { Exists(d, a) => … }`, the theorem took 120 s to elaborate. The
kernel gate then exhausted the 8 GiB address-space rail, with a stack of
`tm_infer_inner`/`tm_check_inner` frames. The same proof written with
`let a = …;` and `a.witness`/`a.proof` projections checks in about 7 s of
elaboration and is accepted by the kernel. The chain rule has six nested
matches, and it went from about 70 s to 6 s the same way.

```heather
// slow: each arm re-elaborates under the motive of every enclosing match
match hf(e1, p1) { Exists(df, af) => match hg(e3, p3) { Exists(dg, ag) => … } }
// fast
let af = hf(e1, p1); let ag = hg(e3, p3); … af.witness … ag.proof.right(…) …
```

Probably each `match` copies its motive, the expected type of the body
with the scrutinee abstracted, into every arm, and the motive grows with
each enclosing binder. To investigate, take `--timings` over the matched
version (in this issue's history) against the projected one, and look at
the motive sizes. The library's convention until then is projections for
any chain of more than two or three `∃` choices.
