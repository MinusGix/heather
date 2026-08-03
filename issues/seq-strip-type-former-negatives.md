---
title: "Pin the type-former face of the head-only strip gap (Vec/Fin/El at a transported canonical index)"
status: open
labels: [kernel,conversion,testing]
created: 2026-08-03
updated: 2026-08-03
---

Found by the ch. 07 FT pass (`docs/metatheory-ch07-extensions.md` §22.4)
and corrected into `docs/sprop-design.md` §5.4: the head-only strip gap has
a *type-level* instance the 2b acceptance's term-level negative does not
cover. With `e : sEq^0(Nat; a; 0)` at convertible-but-stuck endpoints,
`Vec^l(T; transp(…; e; 0))` is a whnf neutral type (`is_neutral_term`
follows the transp's proof, `reduce.rs`; the length stepper is strip-blind)
while `Vec^l(T; 0) ⇝ Unit^l` — so `ty_nf` sees neutral-vs-canonical and
rejects a declaratively convertible pair. Same cause at `Fin(transp(…))`
vs `Empty` and `El(transp(…; TmNat))` vs `Nat`.

Incompleteness only — never an unsound accept, never non-termination — and
confined to redundant casts by §22.3's erasure argument. Closing it would
mean stripping where *reduction* looks for redexes, which is the declined
strip-in-reduce design (TYPES 2024 bill; determinacy); this issue is
therefore **testing, not a fix**.

Owed, next time someone is in `crates/kernel/tests/seq_transp.rs`:

1. A negative pinning `Vec(T; transp(e; 0)) ≢ Vec(T; 0)` at stuck-but-
   convertible endpoints — the literal-length axis the existing
   `vec_at_a_transported_length_strips` test misses (its length is a
   context variable, so both sides stay neutral; this is
   `docs/testing-generated-terms.md`'s first axis, and the sixth live
   defect class that discipline catches).
2. The same at one of `Fin`/`El`, so the "one cause, three positions"
   claim stays pinned from two angles.

Generator-side consequence recorded on [[indexed-families]]: the 2b rule
"never emit a cast at convertible endpoints" must be read as covering
`Vec`/`Wf` **index** and code positions, not only value-level casts.
