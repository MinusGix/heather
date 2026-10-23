---
title: Name a recursive declaration's shape spine components
status: closed
labels: [elaboration,inductives,performance,representation]
created: 2026-09-06
updated: 2026-10-03
---

[[inductive-spelling-codes-nonrecursive]] named the payloads and suffix
sums of **flat** declarations and left recursive ones alone, by charter and
by measurement (no recursive many-constructor type is on the x86 module's
path). A recursive declaration's `D#shape` code is still the inline
sum-of-Σs literal (`⌜S⌝`), so a constructor label's `inl`/`inr` chain
spells its suffix sums out at every level, and the kernel's decode of
`El (D#shape^δ)` meets the label's named-component spelling one level at
a time — the same O(n²)-per-literal cost the flat round removed, on `Ir`,
`Node`, `StructuredRegion` and every other wide recursive declaration.

The mechanism is the same: register `PayloadCode`/`SuffixCode` off the
*shape's* spine (`spine` already reads a `Wf`'s shape), spell `D#shape`'s
body over the names, keep `WfSlots::shape_decoded` as the guard copy of
the decode (it becomes `Sum(El (D#payload₀^δ), El (D#suffix₀^δ))`), and let
`respell_spine`'s positional path do the rest. The unknown is
`wf_slot_refs`' second guard copy and `unspell_shape_here`, which assume
the shape decodes to `El ⌜S⌝`.

## When

Triggered: the next round on a workload with a wide recursive declaration
where the sampler's `El^δ` vs `Sum` or `Sum` vs `Sum` rows are its labels
(the `ir_v1` / certgen fixtures are the obvious candidates). Measure
first with the sampler; one deliberate round.

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns `D#shape`/`D#arity` and their
  guards. Assumed here: only that `shape_decoded` is a second guard copy.
- **[[inductive-spelling-codes-nonrecursive]]** owns the spine-code
  mechanism. Assumed here: only its registration boundary.

## Log

- 2026-10-03: **Landed, measured first** (2026-10-03, cloud box, release `--features value-metrics`, `--kernel-workers 1`; counts exact, seconds rough). Workload: `lib/certgen/ir_v1.hthr` + `lib/certgen/certgen_code.hthr` concatenated (certgen_code is elaborated over ir_v1's prefix and does not check alone). **Before (master 1334d9a):** gate 3.49 s, 12,988 misses, 201,652 queries, 401,790 steps; top rows `Sum`/`El^δ` 606 / 0.52 s and `El^δ`/`Sum` 594 / 0.12 s. **The trigger was half right.** The top row was *not* labels: `HEATHER_CONV_MISS_TRACE=transcribe` showed 57 misses at ~11 ms each of a 44 K-char inline `⟦TA⟧` (flat, tag 24) against `El (TA#tycode^δ)`, at `GlobalTm < ElimCodeTm` — the `match code … as TA` **motive** written inline (`quote.rs`), checked against every branch, each a `ta_*` call whose codomain is the reference. Fixed there: the motive goes through `annotation_type`, minted at the motive's own local scope (Γ plus the scrutinee binder; minted at `mcx` it was a kernel `SubstMismatch`). `transcribe` 67 misses → 1, its steps 77 K → 0.9 K; the whole run's gate 3.49 → 2.92 s. **Then this issue's mechanism**, on top: `register_wf_slots` registers `PayloadCode`/`SuffixCode` off the shape's spine (`register_spine_codes` unchanged; `spine` already unwraps the `Wf`) and spells `D#shape`'s body as `D#payload₀^δ + D#suffix₀^δ`; `respell_spine`'s positional path then names a recursive constructor value's labels with no further edit. Two things the old guard assumed broke and are fixed: (1) `wf_slot_refs` compared `shape_decoded` raw, but the decode copy is `El` of `D#shape`'s **body**, scoped over the Ψ prefix before the definition — it now rescopes by `now − abs(D#shape)` before comparing (this was already stale for any shape with a named field type, since 2026-08-13; it only ever declined, silently); (2) a named decode is a sum of neutral references `tag_of` cannot read, so the guard reads the tag through `unspell_sum_components`. Result over motive-only (two interleaved pairs): gate 2.92 → 2.73–2.79 s, queries 197,586 → 184,713, misses 12,861 → 13,956 (cheap one-δ ones), steps flat. `ir_v1.hthr` alone, one pair: gate 0.65 → 0.55 s, queries 179 K → 167 K. `function_ir.hthr` alone: counts flat (queries −1.3 K), one-sample seconds noise. **Refuted variant:** respelling the `D#arity` body's `Case` annotations by position too (`arity_spine_refs`) moved no miss bucket and raised evaluator steps 321 K → 442 K (`IrCases` 14 K → 106 K): the δs are paid wherever the arity is *computed*. Not landed; the arity stays inline. **Found on the way:** [[match-code-recursive-motive-level-mismatch]] (pre-existing; a `match code` at a recursive motive with a constructor-valued written arm is refused). **Tests:** `wf.rs mod tycode` — the boundary test now covers recursive declarations (`T`, `U`) and keeps parameterized ones out; the decoded-shape guard test pins the named decode; new: the recursive shape's δ+decode and its whnf unspell plus the positional emission spine with the `U` look-alike, the four axes over a recursive declaration with a false-equation control, and a `match code` motive pinned as `El (Flat#tycode^δ)`. Full `scripts/test`: `== suite: 3101 passed, 0 failed, 5 ignored ==`. Closing: scope done; the residue (the arity) is a measured no, and the next rows on this workload are `Id`/`Id` and `Sigma`/`El(?)` (`IrCases`' record projections), neither a spelling of a recursive shape.
