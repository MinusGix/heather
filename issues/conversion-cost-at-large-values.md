---
title: Conversion's own cost on large canonical values: the residual no spelling reaches
status: open
labels: [kernel,conversion,performance]
created: 2026-08-13
updated: 2026-08-13
---

The residual named by two consecutive spelling rounds and owned by neither. After [[wf-field-conversion-cost]]'s component respell and [[wf-shape-annotation-slots]]'s slot naming removed most emitted node mass, `lib/ir_v1.hthr` whole moved least of the measured workloads (~1.25x where the declarations prefix moved ~1.6x and prefix+certgen_code ~3x): its theorems' wall time is **conversion on large values** — the kernel comparing/reducing big canonical constructor trees — which no annotation spelling touches, because the cost is in the values themselves, not their type annotations.

Both rounds' logs name it explicitly ("the residual that no spelling reaches", docs/annotation-component-respell-design.md and docs/wf-shape-code-design.md §7); this issue is its home so the next re-attribution has somewhere to point.

Related but distinct: [[value-domain-allocation-constant]] (the value domain's constant-factor allocation where there is no sharing to win) and the closed [[whnf-sharing-term-growth]] (working-term growth in non-tail eval nesting). Whether this issue's cost decomposes into those or is its own defect is the first thing a round here should measure.

## When

Triggered: the next time `lib/ir_v1.hthr`'s theorem wall time (or any large-value workload's conversion share) matters — one deliberate round, per the accumulator discipline. Measurement first: profile where conversion spends on one of ir_v1's value-heavy theorems before proposing anything.

## Log

- 2026-08-13: THE DENOMINATOR AND THE SHAPE, from the certgen family's post-evaluation attribution round ([[certgen-harness-cost]] owns the round and the per-binary numbers; assumed here only that its phase timers attribute wall to declarations). This issue asked for measurement before proposing anything; here is measurement, plus a reproducer far cheaper than "lib/ir_v1.hthr whole".

WHERE IT IS. In the certgen family (~32 s wall, 2026-08-13) this cost is ~48%: the ungated backstop prefix's four expensive declarations (k_bind_mono 2.49 s, step_mono 1.35, letcall_conv 0.24, letmatch_conv 0.27) plus twelve generated `X_gen_conv` invariant proofs at 0.74-1.18 s each. In every one of them `conv_type` is 84-95% of the kernel-gate time.

THE REPRODUCER: **`k_bind_mono` in lib/ir_v1.hthr -- thirteen lines, 2.49 s to kernel-check, ~2x the 96-line `step_mono` that calls it three times, and the single most expensive declaration in the family.** Its statement is three function-typed parameters (`ev1`, `ev2`, `hyp`) over `Val -> Ir -> Res` and a `j`-transport whose motive is a `k_bind(...) = Out(vs)` equation; its proof is one `k_bind_inv` destructure and one `j`. Iterating on this is minutes, not a whole-library check.

THE SHAPE, and it rules out a whole family of fixes. Bucketed `conv_type` durations for k_bind_mono's check: 121,912 calls in total, of which **92,784 finish in under 1 us and cost 12 ms between them**; 20,712 under 10 us cost 116 ms; and then 1,348 calls at >= 100 us carry 1,557 ms (76% of the 2.05 s), with THIRTEEN calls at >= 10 ms carrying 414 ms (20%). Every generated `_gen_conv` has the same profile (e.g. `seven_gen_conv`: 75,211 calls, 47,595 under 1 us costing 9 ms, 1,567 at >= 100 us costing 693 ms of 1,063). So this is NOT a many-cheap-calls problem: the call count is already essentially free, and [[conv-pointer-equality-reflexivity]]'s landed short-circuits have nothing left to catch. The cost is a small number of individually expensive conversions of big canonical Ir/Val trees, exactly as this issue's body says.

TWO ADJACENT MECHANISMS RULED OUT while attributing, so a round here does not re-test them:
* **Not the rewriter.** `typing.rs`'s `whnf_type_delta` (the reduce.rs term rewriter, which conversion left behind at the NbE round) is 0.0 ms and <= 10 calls on every expensive declaration measured. conv.rs already runs on the value domain. This is not a second [[whnf-sharing-term-growth]] consumer.
* **Not emitted node mass.** Rendered-Psi growth and check time are decoupled by ~150x on this workload: `ta_inr` in lib/certgen_code.hthr adds 289 kB of Psi and checks in 117 ms; k_bind_mono adds 129 kB and checks in 2.43 s. So the two spelling rounds' residual ([[unnameable-annotation-occurrences]], including its family (1) -- fn-typed-parameter App dom/cod annotations, which k_bind_mono is full of) is NOT what is being paid here.

WHAT A ROUND SHOULD DO FIRST: take the thirteen >= 10 ms conversions of k_bind_mono and say what each one is comparing. The body's own question -- whether this decomposes into [[value-domain-allocation-constant]] / the closed [[whnf-sharing-term-growth]] or is its own defect -- is now askable on thirteen concrete cases rather than on a whole library.

TRIGGER RESTATED: this is now the largest single term in the certifying generator's cost AND the only one that scales with its product (each future generated function adds ~0.8-1.2 s of it), which is a stronger trigger than the one this issue was filed with.
