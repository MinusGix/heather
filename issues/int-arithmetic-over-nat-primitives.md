---
title: Int arithmetic through the Nat run primitives
status: closed
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

## Log

- 2026-09-09: LANDED, the library answer. `int::add` is now the four sign cases over `nat::add` and a new `subNatNat(m, n)` (`m - n` as an integer, structural on `m` with `n` synchronized exactly as `nat::sub` is), so every closed sum is one program application on runs: the kernel's Sync class already classifies `subNatNat` (q = 0, the result type is irrelevant to the probe) and `nat::add` is Affine. Measured with the release CLI on furnace: `sub(OfNat(2^63), OfNat(2^64))` and every other sign quadrant at 2^63/2^64 check within noise of the 2 s std-prefix load, and negative `toInt` at width 64 costs about 1 s over it. The kernel option (a sum-typed window class) was not built: the library definition's reduction cost matches its meaning, which is the [[kernel-acceleration-policy]] answer, and it cost no kernel trust. Lemma-kit price, honestly: `addNat`/`subNat` and their eight lemmas are gone; the old definition survives as `add_isucc`/`add_ipred` (four constructor cases each, the non-computing ones a `subNatNat` fact from `isucc_subNatNat`/`ipred_subNatNat`/`subNatNat_zero`), `add_comm` became four cases with the mixed ones `refl`, `isucc_add`/`ipred_add` go through it, and `add_ofnat_ofnat` is `refl`. What was lost is `a + OfNat(0) ≡ a` and `a + OfNat(Succ k) ≡ isucc(a + OfNat k)` at OPEN `a`: `add_zero` is a case split, the two unit steps are `add_one`/`add_neg_one`, and every `int_ind` base and step arm (`add_assoc`, `neg_add`, `mul_add_distr`, `add_le_mono_r`) rewrites by the push lemmas where it was `refl`; `add_neg_cancel_r/l`, the `CommMonoid` right unit, and two sites in `omega.hthr` (`dot_add`, `div_lower_nonzero`) used `add_zero` in a direction that only conversion had made irrelevant. Observation for elsewhere: three of those (`add_le_mono_r`, `mul_add_distr`, the monoid instance) were accepted by the elaborator and rejected by the kernel as NotConvertible, i.e. the elaborator's conversion is more permissive than the kernel's somewhere around `x + OfNat(0)` vs `x` at open `x`; harmless (the kernel gates) but a diagnostic-quality gap, reproduced minimally and filed as [[elab-refl-accepts-match-eta-kernel-rejects]]. Rails: `addition_at_machine_magnitudes_costs_a_payload_operation` in `crates/elab/tests/lib_std_int.rs` and two negative width-64 `toInt` theorems in `lib_std_bitvec.rs`'s width-64 consumer test. The `addNat_zero_l` examples in docs/calc-equational-chains-design.md and docs/congruence-in-inference-position-design.md are now historical.
