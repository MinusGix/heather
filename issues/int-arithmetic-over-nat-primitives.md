---
title: Int arithmetic through the Nat run primitives
status: open
labels: [stdlib,int,arithmetic,performance]
created: 2026-09-09
updated: 2026-09-09
---

[[nat-run-algebra-primitives]] makes `nat::add/mul/sub/leb/half` one program
application on runs. `int::addNat`/`subNat` fold `isucc`/`ipred` over an
`Int`-valued induction hypothesis, which no Nat algebra class covers, so
`int::sub(OfNat(2^63), OfNat(2^64))` is still magnitude-linear.

Two answers, to be costed against the lemma kit:

- **Library.** Define `int::add` on the four constructor cases by `nat::leb`
  and `nat::sub` (`OfNat n + NegSucc m` is `if leb(m+1, n) then OfNat(sub(n, m+1))
  else NegSucc(sub(m, n))`), keeping the current definitions as theorems.
  This is the [[kernel-acceleration-policy]] answer: a definition whose
  reduction cost matches its meaning.
- **Kernel.** A sum-typed window class: probe `ih := Inl(x)` / `Inr(x)` and
  iterate a constructor-indexed affine map. More general, more trust.

The `toInt` width-64 negative rail in `crates/elab/tests/lib_std_bitvec.rs`
is the acceptance probe.
