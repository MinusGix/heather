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

- 2026-08-12: **HYPOTHESIS filed for the fix round's first hour (coordinator, post-round): the 52-branch match-code shells may be this same pathology, which would make the fix the suite's biggest lever, not just this issue's.** Every analyzer shell in `lib/certgen_code.hthr` is a `match` over the reflected code type, ~52 constructors; by this round's own size laws that type's lowered form is ≈ 9·52² ≈ 24k nodes, and a match writes `⟦D⟧` out ~21 times per arm across 52 arms. That shape is consistent with [[certgen-harness-cost]]'s recorded rails — the ~9 s double-j kit lemmas, the ~90 s transcriber positive that is the fast lane's floor, and "each new analyzer shell adds another gate." **Unmeasured**: a hypothesis, not a finding — the shells' scrutinee is a different inductive with its own lowering tier, and the size laws were measured on tier-1. The check is cheap with this round's methodology (node-count one shell's elaborated body, count `Type::Wf` occurrences against the 21a+4 law), so the fix round's charter should spend its first hour on it: if it holds, the payoff estimate changes from "un-tax a workload we designed around anyway" to "collapse the suite's dominant cost and cheapen every future analyzer slot"; if it fails, the fix is still justified by this issue's own 8.5x. The fix itself is [[family-types-as-code-defs]]'s landed pattern (`El (D#code^δ)`, `gen_type_ref`) applied to the tier-1 match lowering's inline `⟦D⟧` copies — that issue is CLOSED and stays closed; the new site needs a tier-1 `D#code` GenDef the forded round never minted, and its migration surface (the structural readers of `Type::Wf`, with `forded.rs mod fingerprint`'s look-alike-negative discipline) is pre-mapped above. [[wf-shape-annotation-slots]] rides along per its own 2026-08-12 note: same fix shape, different slot — the round should scope both and measure which one its fixture is on.

- 2026-08-12: **FIX LANDED (partial, measured), and the coordinator's shell hypothesis is REFUTED — cleanly, and with a more useful answer behind it.** (Fix round; release build, this machine, wall-clock here and nowhere else per [[perf-tracking-consistent-environment]]. Node counts are exact and come from a throwaway `write_exact`-based counter at the two kernel-gate sites, reverted before the final verification, exactly as the measurement round's were. A/B was an env kill-switch on the registration, so both columns are one binary.)

  **PHASE 0 — the hypothesis fails, and the file is the pathology anyway.** The two `match code` shells of `lib/certgen_code.hthr` are *not* this pathology. `check_sig`'s elaborated body is **15,224 nodes with zero `Type::Wf` occurrences** — its motive `SigOut` is a two-constructor non-recursive inductive, and `match code` is a `rec_ga` elimination over the kernel's own code type, not a tier-1 `Wf` match, so the `21a+4` law never applied to it. `transcribe`'s body is **619,981 nodes / 1,258 `Wf`**, real but **3.3% of the file's 18.9 M body nodes**. The hypothesis's arithmetic (52 arms × 21 copies × ~24 k) predicted the shells would dominate; they do not, and the "different inductive, different lowering tier" caveat the coordinator wrote is exactly why.
  **But the file *is* dominated by this issue's mechanism, via a different route**, which is the finding that mattered: `TA` — the walker's accumulator — has a `TBody(body: Ir)` field, and `Ir` is the 1712-node eight-constructor type of law 1. Fifteen ordinary `fn`s `match` on `TA`, and the top of the file's cost is exactly those (`ta_app` 1.37 M nodes, `ta_elim` 1.17 M, `ta_lam` 655 k, `ta_call` 649 k, `ta_val` 599 k, `ta_succ` 563 k). So the payoff class is "the suite's dominant file, through its ordinary program-layer helpers", not "the analyzer shells" — and `TA` is **non-recursive**, which turned out to matter (below).

  **WHAT LANDED.** `GenDef::TyCode(tag)` — `D#tycode : Trm_c(· ⊢ Ty l) := ⌜⟦D⟧⌝`, registered at declaration time through the unchanged `push_gen_def` gate, for an **unparameterized, unindexed** declaration, recursive or not. Emission takes `El (D#tycode^δ)` at the tier-1 telescope's `Vec`/`nth` element slots, `nth_child`, the container `Snd` chain, `build_children`'s `Pair` annotations, `child_projection`'s motive, and — the big one — the `match` **motive**, in both `wf.rs`'s tier-1 lowering and `inductive.rs`'s tier-0 `case_tree`. Structural reads keep the inline copy, per reader, and the table is in `docs/family-type-code-defs-design.md` §10.3. Kernel behavior unchanged; the one kernel edit is `wf_step_telescope_at`, a parameterization of the existing helper so the telescope still has exactly one transcription. **No recognizer was taught to resolve through the registry**, because none can see a reference: every reference goes into an annotation slot and every structural read is taken from a type that arrives inline. Files: `crates/elab/src/gendefs.rs`, `crates/elab/src/wf.rs`, `crates/elab/src/inductive.rs`, `crates/kernel/src/term.rs`.

  **NUMBERS** (wall = best of 3; nodes exact). "off"/"on" is the registration kill-switch.

  | file | wall off | wall on | body nodes off | body nodes on |
  |---|---|---|---|---|
  | `ir_v1` declarations prefix | 0.88 s | **0.62 s** | 4.38 M | **2.89 M** |
  | prefix + landed `certgen_cert` | 1.67 s | **1.15 s** | 7.89 M | **4.89 M** |
  | prefix + the `Ir`-field **draft** (this issue's reproducer) | 14.54 s | **8.23 s** | 51.5 M | **24.1 M** |
  | prefix + `certgen_code` (the shells file) | 34.80 s | **30.65 s** | 19.5 M | **16.2 M** |

  Statement nodes on the draft: 12.5 M → 10.0 M. `Type::Wf` occurrences on the draft: 158,080 → 72,085. Per-declaration on the draft, the shape of the win: `cert_rebind` 9.30 M → 2.35 M (4.0x), `cert_chain` 8.52 M → 3.36 M (2.5x), `cert_body` 21.7 M → 9.22 M (2.4x — and 21.7 → 21.4 with the registration restricted to *recursive* declarations, which is what forced the widening: `cert_body`'s motive is the non-recursive `CertOut`).

  **THE REPRODUCER RATIO IS NOT ERASED: 8.7x → 7.2x.** The prediction recorded above — "the per-field contribution falls to ~130 references, i.e. the whole gap" — was **too strong, and the correction re-homes the residual**. The `21a+4` copies are two families: occurrences of the *whole* `⟦D⟧` (this round's, and they do collapse), and occurrences of its *components* — the spine's per-constructor Σ payload types and the right-nested sum tails, plus the `Supf`/`ElimWf` shape slots — which no whole-type code can name, a sum tail not being a declared type. Both halves fell by ~2.1x in absolute terms; the *ratio* barely moved because the draft and the landed file pay it in the same proportion. Attribution of what is left, measured with per-site counters on the draft: the spine is **38 k nodes of a 21 M body** and the shape slots **1.3 k** — so the residual is *neither* of the two suspects anyone had named. What is left is the per-application `dom`/`cod` annotations (which carry the callee's declared types) and the field-binder projection chains (which carry the constructor's Σ components). Those are a different lever — statement-side respelling (design §8 phase 4) and a projection-chain code — and they are **filed, not taken**; a successor should start from that attribution rather than from this issue's opening suspects, all three of which are now closed.

  **This issue stays open** on that residual, with its own opening question answered (pathology, confirmed; mechanism, found; fix, half-landed and measured).

  **One latent bug found and fixed on the way**: `gen_ref` omitted the `meta_off` that `resolve` has always added for a `meta fn`'s Ψ-extending binders — latent because nothing emitted a generated-definition reference from inside a meta body until the motive respell did. Symptom was a kernel `WrongGlobalBinding` naming the context binder (`crates/elab/tests/certgen_route1_spike.rs`'s meta walk over `Ir`). Fixed in `gen_ref`/`gen_def_of` via `Elaborator::meta_offset`, with a regression test.

  Tests: eleven new in `crates/elab/src/wf.rs mod tycode` — the registration boundary (closed yes / parameterized no), the reference's identity and idempotence and both conversion directions, the four axes of `docs/testing-generated-terms.md` on the tier-1 and tier-0 paths (literal and neutral scrutinee, open element type via `Box<A>`, checking positions, computations pinned by `refl`), a false-equation negative control, the meta-body numbering regression, and three look-alike negatives in `forded.rs mod fingerprint`'s discipline: a type `tag_of` routes to `D` but which is not `⟦D⟧` (the guard's own test — without the registry's inline copy this would be spelled with `D`'s code and decode to something else), `El` of the *wrong* declaration's code, and `El` of a byte-identical user global (identity is the Ψ index, not the body).
- 2026-08-12: The non-Nat-embeddings round (2026-08-12, docs/certgen-non-nat-embeddings-design.md) is the first FEATURE round to be re-shaped by this issue's law rather than merely measured by it, and it contributes two data points the residual-attribution work should keep. (1) NESTING MULTIPLIES, confirmed at a new site: a first cut of lib/certgen_code.hthr's constructor-value recognizer wrote ta_pair as a THREE-level match on TA (match b, then match a, then match ta_val(a)) and by itself took the file from 36 s to well past scripts/test's 300-second per-process ulimit -t -- a SIGKILL, not a slow run. Flattening it into one-match helper fns brought the file to 89 s; the file now states 'one match on TA per fn' as a rule with this issue as its reason. (2) A RETURN TYPE IS A FIELD TYPE: ta_val returned TA, so its three consumers each paid a full TA elimination; narrowing it to a two-constructor VOut { VNo, VYes(pre, res, len) } removed three TA matches and is a strict improvement on the PRE-round file too. Final landed cost 42 s for +2 TA constructors and +6 fns, i.e. +17%. (3) The round's SCOPE was cut by the law: constructor FIELDS on the embedded source type were designed in, then dropped, because a payload state carrying a compiled Pre prefix adds two more Pre fields to TA and Pre -- not Ir -- is that type's largest field; with fields the per-fixture generation cost went 3 s -> 114 s on the one fixture that had one. Recorded there as sec. 2.2 with the table. Nothing here contradicts the fix round's attribution; it is the first evidence that the residual bites at DESIGN time, and that the operative field type at this site is now Pre rather than TBody's Ir.
