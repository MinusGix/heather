---
title: Execute the shared-value whnf plan (nbe-conversion-design §13)
status: open
labels: [kernel,conversion,performance,meta]
created: 2026-07-31
updated: 2026-07-31
---

Execution tracker for the sharing-preserving conversion round. The
*design* lives in `docs/nbe-conversion-design.md` (decided answers,
rejected alternatives, §13 staged plan) and is not restated here; the
*defect* is owned by [[whnf-sharing-term-growth]] (which closes only when
the acceptance instrument goes linear). This issue owns stage status:
each stage logs its landing, gate results, and any deviation from the
doc here.

## Stages (design doc §13; sizes in definitions-rounds)

| stage | what | size | status |
| --- | --- | --- | --- |
| 0 | acceptance instrument: elaborated arm-nested probe, CLI-level, validated ≥1.8×/level ON MASTER | 0.3 | **done** (`scripts/probe-whnf-sharing`) |
| 1 | value domain + evaluator, unwired, differential-tested against the rewriter over `wt.rs` streams | 1.5 | **done** (`src/value.rs`, `src/eval.rs`, `tests/eval_differential.rs`) |
| 2a | conversion arms made shape-agnostic (accessor trait), zero behavior change | 0.7 | pending |
| 2b | conversion switched to values (THE risky stage) | 1.5 | pending |
| 3 | δ glueing: memoized unfolds, per-GlobalVar rescoped-body cache | 0.7 | pending |
| 4 | cleanup: DESIGN.md rewording, bounds.rs re-measured (prediction: conversion's 21% leaves entirely) | 0.5 | pending |

## Standing gates (every stage)

- `scripts/test` fully green; `scripts/bench --check` clean.
- Every direct `heather` run under the ulimit rail (CLAUDE.md).
- Stage 2b additionally: the stage-0 instrument goes exponential→linear —
  concretely, `scripts/probe-whnf-sharing --max 15 --family both --expect
  linear` exits zero, run on the same machine as the master curve recorded in
  that script's docstring,
  routine `lib/ir_v1.hthr` does not regress, and the differential suite
  (rewriter vs evaluator) is green across ≥4 seed streams.

## Kill criteria

- Stage 0: no probe reaches ≥1.8×/level on master ⇒ STOP the round,
  reopen diagnosis on [[whnf-sharing-term-growth]] — the fix would be
  unfalsifiable without the instrument.
- Stage 2b: a conversion-vs-conversion disagreement not traced to a
  *rewriter* bug within one session ⇒ revert to master, re-scope; the
  stage-1 evaluator keeps its value as an oracle-side artifact.

## Log

- 2026-07-31: Filed as the execution tracker after the design round landed (b35a18f, 52a6ecf). Stage 0 dispatched first and separately, per the design round's recommendation: the spike showed hand-built kernel probes stay linear (small-term pointer sharing via the depth-zero fast path), so the instrument must be validated on master before any evaluator code is funded.
- 2026-07-31: **Stage 0 landed and the kill criterion did NOT fire.** The instrument is `scripts/probe-whnf-sharing` (python3, stdlib only, `scripts/issue`'s precedent), deliberately outside both `scripts/test` and `scripts/bench`: a wall-clock threshold in a test rots, the assertion is the ratio between adjacent levels, and §12 already established that this shape cannot be a kernel bench. It generates probe files rather than committing them — each is `lib/ir_v1.hthr`'s declarations (the same cut `crates/elab/tests/ir_v1.rs` makes; there is no import system) plus one generated theorem — so the probe tracks the library instead of drifting from a copy. Every run is under the CLAUDE.md rail, as `resource.setrlimit` on the child; `os.wait4` gives per-run peak RSS. Master curve at 4300b31, baseline-subtracted, N = 1..15: wall 0.06s → 33.77s, peak RSS 0.0 MB → 4544 MB. **Gate held on both quantities**: RSS ratio ≥ 1.8 across five consecutive levels (N = 11..15) with tail geometric mean 2.12, wall three consecutive (N = 10..12, with 13 at 1.79) and tail geometric mean 1.91 — per-level wall ratios wander ±30% with machine load across repeat sweeps, so the geometric mean is the statistic and the run is its sanity check. The negative control (`--family flat`: identical nesting, nothing consuming the nested eval's payload) never reaches 1.8 anywhere and is ~0.04 s / ~0.4 MB per level. N = 15 is the last level under the 8 GB cap. The sweep also sharpened the diagnosis, which is why three variants were built and not one: nesting alone is NOT the axis (13 MB at N=12), nor is a scrutinee value that deepens per level (13 MB), and what multiplies is the pending continuation REBINDING the nested eval's `Out` payload (511 MB) — the issue's surviving hypothesis, isolated in-language. The optional kernel-bench variant was attempted (family D in design §12: the carried argument duplicated at binder depth 1, where `subst.rs`'s own doc says the fast path cannot share it) and measured **linear**, slope 1.44 over twelve levels; it is not the gate, and four hand-built families have now failed where the elaborated probe succeeds. Stages 1 and 2a are unblocked.

- 2026-07-31: **Stage 1 landed, unwired, both gates clean** (`scripts/test` fully green; `scripts/bench --check` "ok: 106 comparisons within thresholds" — nothing is called from `conv.rs`, so nothing moved). Module layout: `crates/kernel/src/value.rs` (936 lines, the domain of §3), `crates/kernel/src/eval.rs` (1370, the machine of §§3–6), `crates/kernel/tests/eval_differential.rs` (1434). Kernel dependencies still zero. Every new recursive type has a `node()`-gated manual `Debug`; `fmt.rs`'s `node()` became `pub(crate)` to serve them. Sharing rather than transcribing, as the design commits: `beta_elim_ty`/`beta_elim_tm` and `Rec` became `pub(crate)` and the evaluator calls them (fired branch comes back as syntax, is evaluated in the current environment — the 52 telescopes are not written a sixth time); `step_type_delta` reduces `elim^Trm`'s Δ-scoped annotation; `nth` is shared by `elim_Wf`'s β.

  **Four places the design was ambiguous or wrong, and what was chosen** — these are what stage 2b should read first.

  1. **Sub-structures are lazy, not values.** §3.3's table writes children as `Val`, which reads as a strict domain. Implemented as `TmClo`/`TyClo` = environment + syntax + memo, forced only where a ch. 06 rule forces (a scrutinee, a `Vec`/`Fin` length, an `El` encoding). A strict domain would agree on every value and still evaluate a never-forced induction hypothesis — §12's family C, whose never-forced ih is the whole point of the round — and would make fuel incomparable with the rewriter's. Consequence for 2b: **every accessor in the shape-agnostic trait is fallible**, because reaching a child is a `force`.
  2. **`VSubst` drops the tail's `k` (and `·`'s base).** THE bug this stage found, and it is a real one for 2b: the tail records the *source* context's length, the rewriter renormalizes it at every `apply_local` (`wk^k_g ∘ δ = wk^δ̂_g`, `subst.rs`'s `SubstLocal::tail`), and a machine that substitutes nothing has no opportunity to. Keeping `k` made a value disagree with its own reduct within 40 seeds. `VTail` keeps only what still discriminates — empty-vs-weakening and which context variable — which is sound because both sides of any comparison live in one scope. `Conv::subst`'s `d1.tail != d2.tail` becomes a `VTail` comparison.
  3. **No `Clo::Native`.** §3.3 offered it for `elim_W`'s and `elim_Wf`'s synthesized ih λ and priced it at two hand-checked cases in §11.2. Not needed: in the environment `(ρ, a, f)` the recursive eliminator is *exactly* `reduce.rs`'s term with `a` and `f` named by de Bruijn slots instead of substituted, so the ih is an ordinary syntactic closure and the whole-node `shift_local(3)` is `reduce.rs`'s `shift_local(1)` widened by two slots. Adequacy is by inspection of the same construction rather than by argument about a Rust closure. §11.2's two hand-checked cases are retired.
  4. **§3.1's "values need the other-namespace maps" does not hold, and nothing here maps a value.** `inst_univ` and `apply_global` renumber the outer scope back *down*, so a closure's captured environment — which is in the outer L and Ψ — is already in the post-instantiation scope. Entering a `UPi`/`CtxPi`/`TyPi` binder instantiates the body *syntax* and leaves the environment alone. The one thing that could break this, a context-variable splice changing Γ's shape, cannot arise: the `g` a `CtxLam` binds is fresh, so it is never Γ's base. This deletes the design's "largest chunk of new surface that is not the evaluator".

  Two smaller notes. `Vec`'s Σ-tail and `Fin`'s `Sum` reach the predecessor by **reifying it into the environment** under a slot the body names with a `Var` — the predecessor is a value with no syntax, and evaluating the tail eagerly would unroll the whole tuple type at a literal length. And `fire`'s final `apply_local(id_Γ, payloads)` was **not** turned into environment extension (§3.5 wanted it to be): it is inside the shared `beta_elim_*`, splitting it would touch 52 call sites, and code recursors are metaprogram-path, not the IR hot path. Filed as a follow-up only if stage 4's re-measurement says it matters.

  **Differential suite.** Agreement is §11.2's relation in its strongest checkable form: head constructors agree, every child is compared, and a closure is entered by applying it to a fresh neutral variable while the syntax side pushes the matching context entry — deliberately the mechanism 2b's η arms will use, so 2b inherits tested machinery. Recursion bounded at depth 5. Under a binder the two sides use *different index spaces* on purpose; the one equation they share is that a value bottoming out at a variable has de Bruijn **level** = the syntax's `len − 1 − i`, with the abstract prefix counted by depth (§3.2). Seed budget: **five streams × 600 cases**, generator budget 8, each stream run **both δ-transparent and δ-opaque** — (1) generated term *and* its type; (2) `perturb_conv` twins, i.e. β/η/letbox/elim_Nat expansions that must actually reduce; (3) open terms at a *checked* type in a forced-non-empty Γ over both `CtxBase` shapes, plus every Γ entry type in its own prefix; (4) identity code recursors, each also wrapped in a β-redex so the environment is longer than the Γ its reduct lives in; (5) a definition-carrying Ψ (`u : Trm_c((·, x:Nat) ⊢ Nat) := <generated>`) with `u^δ` at four payloads × three nesting depths — §3.4's own requested test. Plus three fuel properties stated as *invariants, not thresholds* (§6's warning about asserting a cost model): no budget ever yields a disagreeing value; a thunk that failed under a small budget succeeds when re-forced under a larger one, checked on both an ordinary suspension and a glued neutral's unfolding; zero fuel reduces nothing on either side. Runtime **0.25 s** debug-profile. Failures report seeds only. Negative control: mutating `Env::identity` by one level fails five of the eight tests.

  **Two coverage gaps, both owned by 2b.** (a) The recursors' `motives`/`branches` are not compared: they are the only Γ-scoped raw syntax a value carries (`apply_local` descends into them via `map_branches`, while `other_ty`/`other_ctx` protect every *other* syntactic field — the Δ contexts, box payloads, `elim^Trm`'s annotation, `@Δ`, `@T`), so the rewriter rewrites them at every enclosing β and the machine does not. They agree only *through* the elimination's stored `env`, and reaching them needs the branch telescopes' arities — i.e. `rec_ca`. (b) Consequently `fire`'s `id_Γ` at a scope longer than the reduct's Γ is exercised (stream 4's β-wrapper) but not *sharply*: the identity branches never mention a Γ local, so an off-by-one in the materialized Γ length is currently undetected. A branch that mentions Γ would catch it; building one needs `wt.rs`'s private `BRANCH_DIMS`.

  **No rewriter bug was found.** The one disagreement class the suite produced (the tail `k`) was the *value* side's, and is fixed above.
