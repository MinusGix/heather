---
title: A Wf-lowered inductive as a field of another inductive costs ~163x: pathology or law?
status: open
labels: [kernel,elaboration,performance,conversion]
created: 2026-08-12
updated: 2026-08-12
---

Filed from round A (2026-08-12, docs/certgen-cert-expression-design.md): the
first `Cert` draft carried `rest`/`after: Ir` fields — faithful to the kit
lemmas' argument lists — and `lib/certgen_cert.hthr` elaborated in **163
CPU-s**; dropping the fields gave **1.0 s**. A single `match` on the
`Ir`-carrying `Cert` was 4–7 s, a nested one 25–46 s. The final design is
better *on its own merits* (the chain is its own IR, and the renderer is where
the renumbering already lives), so nothing is blocked — but the magnitude
smells like a **pathology, not a law**, and the user's standing position
(2026-08-12) is that perf surprises of this kind usually mean "make the
kernel/elaborator smarter or fix a pathology", not "design around it". This
issue owns finding the mechanism before anyone treats the workaround as a
design rule.

Suspects, unweighed:

- the tier-1 lowering of a constructor whose *field type* is itself Wf-lowered
  (a `Supf` label carrying a `Supf`-typed payload) — does the
  children-container encoding nest a whole second telescope per constructor?
- conversion/`refl` between values of such a type: the round's own note says a
  `refl` between two Wf-lowered values is "the expensive kind of pin" — is the
  cost in `conv_term` re-walking the nested `Supf` spines without sharing
  (cf. the closed whnf-sharing-term-growth mechanism)?
- the elaborator's `match` lowering over the nested shape (the 4–7 s single /
  25–46 s nested gradient points at per-arm motive/telescope rebuilding).

Reproducer: reconstruct the draft datatype from the design doc (§2 records the
field-carrying shape) beside the landed one; the 163× is the gap between the
two elaborations of one file. Measure per the recorded protocol only
([[perf-tracking-consistent-environment]]); a named candidate workload for the
instruction-count harness once it exists.

Trigger: the next time anyone wants an inductive carrying a Wf-lowered field
([[nested-inductives-container-fields]] is adjacent), or the next deliberate
perf round. Related: [[certgen-harness-cost]] (where the observation was first
logged — its "rule of thumb: don't embed" should be read as a marker of THIS
issue, not as design doctrine).

**Answered 2026-08-12 (see the Log): pathology, not law.** The mechanism is
the elaborator's tier-1 `match` lowering writing `⟦D⟧` out Θ(arms) times, with
each copy carrying every field type's lowered form verbatim; the kernel then
does work strictly linear in what it is handed. The predicate is *not*
"Wf-lowered" — it is the SIZE of `⟦T⟧`, which is quadratic in `T`'s
constructor count. Nothing landed: the fix is [[family-types-as-code-defs]]'s
`El (D#code^δ)` applied to the tier-1 lowering, whose migration surface is the
structural readers of `Type::Wf`, and that is a round of its own.


## Log

- 2026-08-12: **MECHANISM FOUND — pathology, not law; nothing landed, deliberately.** (Deliberate perf round, release build, this machine; wall-clock here and nowhere else, per [[perf-tracking-consistent-environment]]. Peak RSS stayed at 12–15 MB for every run below, which is itself a finding.)

  **Reproducer** (scratch, not committed; recipe, because it generates rather than copies — same convention as `scripts/probe-whnf-sharing`). Every file is `lib/ir_v1.hthr` cut at its first `\ntheorem ` (the cut `crates/elab/tests/*.rs` make) plus a generated tail, checked with `(ulimit -v 8388608 -t 120; target/release/heather check -L lib/std <file>)`; the two full-draft runs were given `-t 300`/`-t 600` deliberately. The draft is `lib/certgen_cert.hthr` with `rest: Ir` on `CCon`/`CIh`/`CCall`, `after: Ir` on `CMatch`, and the fold and the six `refl` pins respelled to carry them — i.e. the design doc §2 shape, diffed against the landed file to confirm nothing else moved. Baseline (declarations prefix alone): 0.80 s.

  **Reproduction: the direction reproduces, the constant does not.** Landed file on the prefix 1.62 s; the faithful draft 13.8 s. That is **8.5x, not 163x**. The design doc says the first cut *also* carried six `Cert` eliminations (stuckness propagated through smart constructors, "~90 CPU-seconds of the 163"); reconstructed here — a `Cert`-returning total match on the `Ir`-carrying `Cert` — each costs 2.4 s and a smart-constructor-shaped one 2.8 s, so six bring the draft to ~30 CPU-s, still 5x short of 163. Either the first cut had more elimination sites than §2 records, or the 163 was a dev-profile harness number. **The ratio's mechanism is fully characterised below; the constant 163 should not be quoted again.**

  **The ladder** (baseline-subtracted, plain → `Ir`-field): declaring the inductive 0.05 → 0.05 s; one `refl` pin between two `Cert` values 0.03 → 0.45 s; one total `match` on `Cert` 0.07 → 1.22 s; a nested match 0.12 → 2.98 s (≈ two matches — the "nested multiplies again" of the original note is just *more matches*, the growth is linear in match count).

  **Per-declaration attribution** (scratch counters at the two kernel-gate sites, `crates/elab/src/lib.rs` and `gendefs::push_gen_def`; counters in `conv.rs`/`subst.rs`/`typing.rs`/`eval.rs`; a throwaway patch, now reverted, exactly as [[whnf-sharing-term-growth]]'s round did it). The single `match` declaration's elaborated **body goes 65,475 → 1,708,035 nodes (26x)** and its statement 1,452 → 37,383 (26x). Every kernel counter tracks that 1:1: conversion roots 5,106 → 133,617; conversion fuel spent 111 k → 4.29 M; substitution node-visits 100 k → 2.94 M; `ty_check` calls 61.8 k → 1.61 M; value-machine `eval_ty` 211 k → 8.12 M. A cache-warm run (`--cache-dir`, which skips only the kernel gate) puts **~95% of the whole file's cost in the gate**: the draft is 14.2 s cold, 0.77 s warm.

  **The kernel is linear in what it is handed.** Sweep: an `a`-arm container, each arm carrying one `Ir` field, `a` = 1..6 — body nodes 45 k → 2.97 M (66x), `ty_check` 45 k → 2.79 M (62x), wall 35 ms → 2.17 s (62x). One ratio, three quantities, no exponent anywhere in the kernel.

  **The sweep shapes**, so the laws below are re-runnable without the scratch files: the width family is `inductive F { F0, Fi(ai: Nat, ri: F) }` for i = 1..n-1, sized by `fn probe(x: F) -> Nat { 0 }` (whose statement is essentially `⟦F⟧`); the container family is `inductive Box { BNil, Bi(x: T, r: Box) }` for i = 0..a-1 with the `x: T` field present on the first `f` of them, eliminated by one total `fn box_head(b: Box) -> Nat { match b { … } }`, and the copy count is `(|body(f=1)| − |body(f=0)|) / |⟦T⟧|`.

  **The three size laws that produce the term** (all measured, not derived):
  1. `|⟦F⟧|` for an `n`-constructor tier-1 inductive is **quadratic in n**: 74, 149, 242, 353, 482, 794, 1178, 1634 nodes at n = 2,3,4,5,6,8,10,12 — constant second difference 18, so ≈ 9n². Hence `⟦Nat⟧` = 3, `⟦Refs⟧` = 58, `⟦Val⟧` = 80, `⟦Ir⟧` = **1712**, `⟦Prog⟧` = 3484.
  2. A field of type `T` adds ≈ **3·|⟦T⟧|** to the container's own `⟦D⟧` — the field type is written out three times in `D`'s sum-of-Σs shape.
  3. The elaborated term of one total `match` on an `a`-arm container contains ≈ **21a + 4 copies of each carried field type**: 25.6, 62.9, 84.5, 106, 128, 149, 193, 236 copies at a = 1,2,3,4,5,6,8,10 (carrier `Refs`; read off both the node totals and the `Type::Wf` occurrence counts, which agree). The factor is a property of the *container's* lowering and is independent of the carried type: at a = 5, one field of `Nat`/`Refs`/`Ir`/`Prog` adds 260 / 7,410 / 222,430 / 452,530 nodes — 87 / 128 / 130 / 130 copies.

  So a match term is **Θ(arms × Σ_fields |⟦T⟧|)**, and `Ir` is expensive for exactly one reason: `|⟦Ir⟧|` = 1712 because `Ir` has eight constructors and law 1 is quadratic.

  **Verdict per suspect.**
  - *(a) the tier-1 lowering of a constructor whose field type is itself Wf-lowered.* **Refuted as a cost, confirmed as the setup.** Declaring the `Ir`-carrying `Cert` is free to the counter — `r1_ind_field` and `r1_ind_plain` produce byte-identical counter totals and both equal the bare baseline. What the declaration does do is law 2: `⟦Cert⟧` acquires three verbatim copies of `⟦Ir⟧`, which is what every later occurrence of `⟦Cert⟧` then carries.
  - *(b) conversion re-walking nested `Supf` spines without sharing.* **Refuted as the driver.** Every conversion quantity is proportional to the term handed to the gate; peak RSS is flat across the whole ladder; there is no exponent. [[whnf-sharing-term-growth]]'s discriminating signature — one exponent shared by time and memory, a working term that grows — is absent, and that defect is closed anyway. The `refl`-pin rung (0.03 → 0.45 s) is real but is the same size law applied to a pinned value, not a separate mechanism.
  - *(c) the `match` lowering.* **Confirmed, and refined.** Not per-arm motive rebuilding as such: `⟦D⟧` is written out Θ(arms) times across the branches — child projections' `Vec` element types, the Σ `fst_ty`/`snd_ty`, the `Pi` domains, the scrutinee annotations (`crates/elab/src/wf.rs`: `wf_branch`, `nth_child`, `build_children`) — and each copy carries every field type inside it.

  **Two exonerations worth recording so nobody re-suspects them.** (i) `Conv::new`'s `has_defs` scan of Ψ is not a cost: it short-circuits after 5 bindings on average (1.2 M scanned across 240 k roots), Ψ = 69 bindings. (ii) The `Supf`/`ElimWf` **shape annotation slots** of [[wf-shape-annotation-slots]] are **not** this: the draft's match body carries one `ElimWf`, no `Supf`, and 7,163 shape-slot nodes out of 1.71 M (a `Cert`-returning match, which does emit six `Supf`, is 50,141 of 2.76 M — 1.8%, same verdict). This is a *sibling* site — the ordinary type annotations of the tier-1 match lowering — not that issue's.

  **The fix, sized but not taken.** Name `⟦D⟧` once: the mechanism already exists as [[family-types-as-code-defs]]'s `El (D#code^δ)` (`gendefs::GenDef::SkelCode`/`IdxCode`, `gen_type_ref`), it is only registered for forded families' components, and `wf.rs`'s tier-1 match lowering spells `⟦D⟧` inline everywhere. Predicted effect: the per-field contribution falls from ~130·|⟦T⟧| to ~130 references, i.e. the whole gap. **Not landed here**, because the migration surface is precisely the line that round held — every structural reader of `Type::Wf` (`const_elim_wf`'s `let Type::Wf { .. } = d_ty.shift_local(d0) else`, `build_children`, `nth_child`, `spine`, `build_elim_wf`, and `forded_of`/`indexed_of`'s fingerprints) pattern-matches `⟦D⟧` directly and would need the same look-alike negatives. That is a round with its own charter, not a rider on a measurement round.

  **Corrections to what was recorded.** (1) "163x" is not reproducible from §2's shape — see above. (2) "A Wf-lowered inductive as a FIELD" is the wrong predicate: `Refs` and `Val` are Wf-lowered too and cost 58 and 80 nodes, i.e. nothing. The predicate is `|⟦T⟧|`, quadratic in `T`'s constructor count. (3) [[certgen-harness-cost]]'s "don't embed" rule of thumb is **not retired** (the pathology is unfixed) but should be restated: *a field whose type has many constructors multiplies every `match` on the container by Θ(arms × |⟦T⟧|)* — Wf-lowering is not the operative word.

  No production code was changed (the scratch counters were reverted before the run); full `scripts/test`: 1463 passed, 0 failed, 0 ignored — the same count as the pre-round commit, as a measurement-only round should give.
