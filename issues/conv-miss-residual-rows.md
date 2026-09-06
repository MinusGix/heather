---
title: The two residual sampler rows the audit left: refl's element type, and constructor literals against respelled field types
status: closed
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

## Log

- 2026-09-06: CLOSED by [[emission-spelling-chokepoint]]'s round (2026-09-06). Both rows were run through the walker and the chokepoint; neither was a spelling pair. **Refl**: `Term::Refl { ty }` now goes through `emit_ty` (expr.rs, `Refl` and `AutoRefl` arms), but the walker never listed `Refl.ty` on the five-node module, and the printed excerpt shows why: the top item's element type is `Nat`, the lhs agrees syntactically and the first difference is the rhs endpoint (`21` vs the computation) — the row is endpoint computation, and the 20–30 % guess was wrong. `Id`/`Id`: 49 / 0.182 s before, 49 / 0.182 s after (furnace, same box; kernel 0.725 s → 0.700 s, box noise). **Constructor literals**: the kernel infers an `inl`/`pair`'s type from its component annotations, so there is no slot in which the inferred side could carry `El (D#tycode^δ)`; the walker lists no `Inl`/`Inr`/`Pair`/`Supf` slot of a constructor label on the library, and the label's annotations are already what `emit_ty` writes (pinned: `wf.rs mod tycode`, `a_constructor_literal_and_the_field_type_it_fills_are_each_the_chokepoints_spelling`). `El^δ`/`Sum` 8,587 / 0.051 s → 8,578 / 0.047 s (~5 µs/query), `El^δ`/`Sigma` 1,880 / 0.036 s → 1,880 / 0.035 s (~19 µs/query): one δ and a compare each, the reference spelling's designed cost, and the only way to make them syntactic is to inline the tails again (the pre-spine-codes design, rejected). The three `Refl.ty` slots the walker does list on the library are generated `Refl`s riding with a rewrite, not expr.rs's — owned by [[emission-walker-residual-sites]].
