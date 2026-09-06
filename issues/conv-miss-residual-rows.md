---
title: The two residual sampler rows the audit left: refl's element type, and constructor literals against respelled field types
status: open
labels: [elaboration,performance]
created: 2026-09-06
updated: 2026-09-06
---

The top of the `Tc::conv_ty` miss sampler on the five-node FunctionIR/x86
module after [[emission-site-respell-audit]] (2026-09-06, kernel 0.87 s):

- `Id` vs `Id`, 49 queries / 0.19 s, `check:Refl` at a theorem's statement
  (`preserves_protected` 14, `byte_length` 1, `gprs_congruent` 8). The
  endpoints genuinely compute, so the row is not a spelling pair — but the
  excerpt also shows the `Id`'s *element type* differing: `Term::Refl { ty }`
  copies `ty` off `read_expected_type` (the inline elaboration-time
  expected), while the kernel's expected is the cascade-respelled statement.
  Spelling `ty` alike (`respell_emitted` at `expr.rs`'s `Refl`/`AutoRefl`
  emission) does not remove the endpoint conversion but lets the kernel skip
  the type half; guess 20–30 % of the row.
- `El^δ` vs `Sigma`, 1,880 queries / 0.08 s, and `El^δ` vs `Sum`, 8,587 /
  0.07 s, `check:Pair`: a constructor literal's inferred type (inline, off
  the label tuple's own annotations) against a respelled field type
  (`Flags(cf := False, …)`-style, `build_fields_skel`'s `fst_e`). One δ and a
  compare each — the cost the reference spelling is meant to have — but the
  largest counts on the board. If `build_ctor` emitted the label at the
  declaration's type *reference* where one exists (the inferred type of a
  `sup_f`/`inl` is its own annotation, so this is the `Inl`/`Inr` and tuple
  annotations spelling the whole type as `El (D#tycode^δ)` rather than its
  components), the row would be syntactic.

Neither is worth a round alone; both are what [[emission-spelling-chokepoint]]'s
walker would list first, so they are filed as its first two targets.

## What it assumes from elsewhere

- **[[emission-spelling-chokepoint]]** owns the mechanism. Assumed here: only
  that a walker exists or will.
- **[[perf-profile-build-target]]** owns the sampler.
