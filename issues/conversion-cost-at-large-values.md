---
title: Conversion's own cost on large canonical values: the residual no spelling reaches
status: closed
labels: [kernel,conversion,performance]
created: 2026-08-13
updated: 2026-08-14
---

The residual named by two consecutive spelling rounds and owned by neither. After [[wf-field-conversion-cost]]'s component respell and [[wf-shape-annotation-slots]]'s slot naming removed most emitted node mass, `lib/certgen/ir_v1.hthr` whole moved least of the measured workloads (~1.25x where the declarations prefix moved ~1.6x and prefix+certgen_code ~3x): its theorems' wall time is **conversion on large values** — the kernel comparing/reducing big canonical constructor trees — which no annotation spelling touches, because the cost is in the values themselves, not their type annotations.

Both rounds' logs name it explicitly ("the residual that no spelling reaches", docs/elaborator/annotation-component-respell-design.md and docs/inductives/wf-shape-code-design.md §7); this issue is its home so the next re-attribution has somewhere to point.

Related but distinct: [[value-domain-allocation-constant]] (the value domain's constant-factor allocation where there is no sharing to win) and the closed [[whnf-sharing-term-growth]] (working-term growth in non-tail eval nesting). Whether this issue's cost decomposes into those or is its own defect is the first thing a round here should measure.

## When

Triggered: the next time `lib/certgen/ir_v1.hthr`'s theorem wall time (or any large-value workload's conversion share) matters — one deliberate round, per the accumulator discipline. Measurement first: profile where conversion spends on one of ir_v1's value-heavy theorems before proposing anything.

## Log

- 2026-08-13: THE DENOMINATOR AND THE SHAPE, from the certgen family's post-evaluation attribution round ([[certgen-harness-cost]] owns the round and the per-binary numbers; assumed here only that its phase timers attribute wall to declarations). This issue asked for measurement before proposing anything; here is measurement, plus a reproducer far cheaper than "lib/certgen/ir_v1.hthr whole".

WHERE IT IS. In the certgen family (~32 s wall, 2026-08-13) this cost is ~48%: the ungated backstop prefix's four expensive declarations (k_bind_mono 2.49 s, step_mono 1.35, letcall_conv 0.24, letmatch_conv 0.27) plus twelve generated `X_gen_conv` invariant proofs at 0.74-1.18 s each. In every one of them `conv_type` is 84-95% of the kernel-gate time.

THE REPRODUCER: **`k_bind_mono` in lib/certgen/ir_v1.hthr -- thirteen lines, 2.49 s to kernel-check, ~2x the 96-line `step_mono` that calls it three times, and the single most expensive declaration in the family.** Its statement is three function-typed parameters (`ev1`, `ev2`, `hyp`) over `Val -> Ir -> Res` and a `j`-transport whose motive is a `k_bind(...) = Out(vs)` equation; its proof is one `k_bind_inv` destructure and one `j`. Iterating on this is minutes, not a whole-library check.

THE SHAPE, and it rules out a whole family of fixes. Bucketed `conv_type` durations for k_bind_mono's check: 121,912 calls in total, of which **92,784 finish in under 1 us and cost 12 ms between them**; 20,712 under 10 us cost 116 ms; and then 1,348 calls at >= 100 us carry 1,557 ms (76% of the 2.05 s), with THIRTEEN calls at >= 10 ms carrying 414 ms (20%). Every generated `_gen_conv` has the same profile (e.g. `seven_gen_conv`: 75,211 calls, 47,595 under 1 us costing 9 ms, 1,567 at >= 100 us costing 693 ms of 1,063). So this is NOT a many-cheap-calls problem: the call count is already essentially free, and [[conv-pointer-equality-reflexivity]]'s landed short-circuits have nothing left to catch. The cost is a small number of individually expensive conversions of big canonical Ir/Val trees, exactly as this issue's body says.

TWO ADJACENT MECHANISMS RULED OUT while attributing, so a round here does not re-test them:
* **Not the rewriter.** `typing.rs`'s `whnf_type_delta` (the reduce.rs term rewriter, which conversion left behind at the NbE round) is 0.0 ms and <= 10 calls on every expensive declaration measured. conv.rs already runs on the value domain. This is not a second [[whnf-sharing-term-growth]] consumer.
* **Not emitted node mass.** Rendered-Psi growth and check time are decoupled by ~150x on this workload: `ta_inr` in lib/certgen/certgen_code.hthr adds 289 kB of Psi and checks in 117 ms; k_bind_mono adds 129 kB and checks in 2.43 s. So the two spelling rounds' residual ([[unnameable-annotation-occurrences]], including its family (1) -- fn-typed-parameter App dom/cod annotations, which k_bind_mono is full of) is NOT what is being paid here.

WHAT A ROUND SHOULD DO FIRST: take the thirteen >= 10 ms conversions of k_bind_mono and say what each one is comparing. The body's own question -- whether this decomposes into [[value-domain-allocation-constant]] / the closed [[whnf-sharing-term-growth]] or is its own defect -- is now askable on thirteen concrete cases rather than on a whole library.

TRIGGER RESTATED: this is now the largest single term in the certifying generator's cost AND the only one that scales with its product (each future generated function adds ~0.8-1.2 s of it), which is a stronger trigger than the one this issue was filed with.

- 2026-08-14: ATTRIBUTED, FIXED, CLOSED. Design and rejected alternatives: docs/kernel/conversion-large-values-design.md; the mechanism in one line is that **the cost was reflexivity paid at full structural price** — a missed short-circuit, not the value domain's accepted constant.

THE THIRTEEN (the round's mandated first question, answered by a site-tagged probe on the public `conv_type` with a deep `==` control per call; release, warm, reproducer = ir_v1.hthr truncated after k_bind_mono). All of them enter from ONE seam — `Tc::tm_check`'s fallback arm, expected-vs-inferred (zero from the Lam-domain premise, zero from elaborator unification, zero root `conv_term` calls at all) — and all of them compare `Id`-types whose endpoints are the big Wf-encoded canonical trees (supf/pair/inl/inr over Σ-tuple children under an app spine of library globals; the Debug prints of A and B are visually identical for the first 512 nodes). The split: **nine of the sixteen calls ≥ 10 ms were deep-`==` EQUAL** — two separately built copies of one type, never pointer-equal, so every landed shortcut of [[conv-pointer-equality-reflexivity]] missed them; `==` on those pairs costs 15-120 us where the structural walk cost 14-46 ms (300-1000x). The remaining seven share a giant equal prefix with a real difference deep inside — NOT a level spelling (`normalize_levels` equality tested per call, never held) — and their cost is genuine reduction + comparison. And it is not only the thirteen: of the reproducer's 153,352 `conv_type` calls, **148,680 (97%) compare syntactically equal inputs**, carrying 1.25 s of the 1.97 s total.

THE FIX (kernel, three small pieces, fuel policy unchanged — every hit spends the node's one unit):
* `Conv::ty_root` (crates/kernel/src/conv.rs): equal roots settle by syntactic reflexivity — `a == b` after the existing borrowed-object check. α-equality is `==` under de Bruijn; `==`-equal levels are trivially equiv; a failed `==` stops at the first difference.
* `Values::ty_eq_fast` / `Values::tm_identity_fast` (conv/dom/values.rs): a hit no longer needs the same closure pointer — two Syn closures over the same environment spine (`value::Env::ptr_eq`, new, head-pointer identity) with `==`-equal bodies denote the same object; `home`/`sat` gating unchanged. Catches the equal endpoint/spine subtrees inside the root-unequal seven.
* Raw term roots untouched (re-measured: still zero hits, matching the closed round). Entry-wise env comparison implemented, measured (zero additional wins), reverted.

NUMBERS (release, warm, ulimit-wrapped): the reproducer file 2.20 -> 0.88 s, its k_bind_mono share ~1.83 -> ~0.61 s; reproducer conv_type total 1.97 -> 0.62 s, the 148,680 equal calls 1.25 s -> 9 ms; whole `lib/certgen/ir_v1.hthr` 5.44 -> 2.15 s. Certgen family per-binary warm (scripts/test --test X, three passes, 2026-08-14 vs the 2026-08-13 protocol run): certgen 0.61 -> 0.68 (noise band), cert 1.40 -> 1.27, controls 7.42 -> 6.78, emissions 15.6 -> 10.2, nonnat 7.35 -> 5.19 — **family 32.4 -> 24.1 s**. Verification: full `scripts/test` 1496 passed, 0 failed (1495 + one new closure-fast-path unit pin; the one-unit fuel pin for root types updated to the new behavior with a convertible-but-unequal OutOfFuel control); `scripts/bench --check` 18 comparisons within thresholds, including the `conv/*` families whose perturbed corpus exercises the failed-`==` path.

WHAT REMAINS is the unequal ≥ 100 us band (~0.55 s of the reproducer's 0.62): real reduction and comparison of genuinely different sides, which decomposes into [[value-domain-allocation-constant]]'s accepted constant (verdict cross-logged there). If a workload ever makes THAT matter, the lever is that issue's list, not this file.
