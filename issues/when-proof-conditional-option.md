---
title: Build When<T, P>, a value present exactly when P holds
status: open
labels: [language,elaborator,library]
area: language
created: 2026-11-14
updated: 2026-11-14
---

`When<T, P>`: a value that is there exactly when `P` holds. Minus's
"proof-conditional Option" (2026-11-14), designed in `docs/when-design.md`,
which owns the type, the tested call, the flow facts, `?` and the coercion.

The issue tracks the build, one PR per stage (`docs/when-design.md` §9):

1. The type and its library, `lib/std/core/when.hthr`, probes in
   `lib/_tests/std/core/when_tests.hthr`.
2. The tested call: a proof-taking call where a `When` is wanted leaves its
   condition out and tests it (no keyword; Minus 2026-11-14 declined a
   `checked` prefix). Run the §7 probes here.
3. Flow facts (`if let` leaving `¬P` in `else`) and `val`'s `known` search.
4. `?` in a function returning `When<U, Q>`, with `Q` stated, on a `When`
   or a proof-taking call.
5. Coercion of a `When<T, P>` to `T` with `P` found, with `scripts/perf ab`
   benchmarks.

Open for Minus (§10): the name, whether `if let`'s negative
evidence is for `When` alone.

## What it assumes from elsewhere
- **[[found-proof-differs-across-recursion-companions]]** (closed) owns the
  lifting of found proofs out of `decreases` bodies. Assumed here: only
  that a proof-taking function's condition is a parameter whose default is
  a context search, as `Vec::at`'s is (PR #607).
- **[[if-evidence-hidden-from-tactics]]** owns the `__if_bitN` names; stage 3
  reuses the device for `if let` evidence.

## Log
