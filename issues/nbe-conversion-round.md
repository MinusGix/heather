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
| 2a | conversion arms made shape-agnostic (accessor trait), zero behavior change | 0.7 | **done** (`src/conv/dom.rs`) |
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

- 2026-07-31: **Stage 2a landed; all three zero-change gates held.** `scripts/test` fully green, `scripts/bench --check` "ok: 106 comparisons within thresholds", and `scripts/probe-whnf-sharing --max 12 --family both` still draws the master curve (nest 9.9 MB → 510.7 MB over twelve levels, tail RSS geometric mean 1.86; flat control 13.1 MB and never above 1.25) — the instrument is untouched, as it must be before 2b can use it as a verdict. The boundary is `crates/kernel/src/conv/dom.rs` (1780 lines); `conv.rs` stays the same size and the same shape.

  **What the trait looks like.** `Dom` has five carriers — `Ty`/`Tm` (a form already in whnf), `TyC`/`TmC` (a *sub-structure* of one), `Subst` — plus `RecCtx`, the scope a code recursor's Γ-scoped raw syntax is read in. `Conv` is `Conv<D>`; the public entry points instantiate `Syn`. Three kinds of member:

  1. **Views** (`TyView`, `TmView`): head discriminant with typed children, levels and local contexts borrowed (they are syntax in both domains, §3.1), children owned. One variant per `Type` former; for terms, only the forms conversion inspects, with `TmView::Opaque` for `λ`/`Λ`/pairs/`⟨⟩`/`srefl` — every rule that could see those is type-directed η, an irrelevance arm, or the neutral catch-all, exactly as before.
  2. **Fallible head-reaching**: `whnf_ty`/`whnf_tm` and their δ-opaque and δ-resume forms, `head_tm` (a sub-structure that is already whnf because the form carrying it is), `as_child_ty`. All `R`-returning from the start, per stage 1's note 1.
  3. **The operations with no common syntax**: `inst_ty`/`inst_tm` (substitution here, closure application there), the four `eta_*` (which take *both* sides so shared annotations stay shared), `embed_ty`/`embed_ty_at`, `push_entry`/`push_spec`, the synthesized formers (`pi`, `vec`, `el`, `sum`, `w`, `wf`, `id`, `nat`, …) and terms (`app`, `proj`, `inj`, `sup_at`, `refl`, `succ`, `local`, `box_ty`), `wf_step_telescope`, `inst_ty_motive`/`inst_tm_motive`, `apply_subst_ty`, and `subst_tails_agree`.

  **Deviations from the doc's sketch, and the arms that resisted.**

  - **The views are total.** §13 and the stage-1 handoff both say every accessor is fallible; that is right for everything that *reaches a head* and wrong for the views, which inspect a form already in whnf and cannot reduce. Making them `R` was not just noise: the `Result` wrapper cost a measurable copy per node (see below). Fallibility lives one step earlier.
  - **`weaken` is not enough for a body under a binder.** `elim_W`'s step telescope writes `t1.shift_local(1)` / `.shift_local(2)` where `t1` is `W`'s *positions*, i.e. a body under the shape binder. A whole-node shift of such a body is not a weakening — it re-scopes the binder onto a new variable — and at values it is closure application, not a no-op. Those three sites became `inst_ty(t1, [a])`, which is equal as syntax and is the operation the value domain actually has. The same pitfall in reverse produced `sup_at`: `sup`'s annotations come from destructuring the *weakened `W` type* rather than from separately weakened children, because only the type knows which of its parts sit under the binder.
  - **`Conv::subst`'s tail test is a predicate**, `subst_tails_agree`, not `==`. The syntax instantiation still compares `SubstTail` in full (including the source length `k`); `VTail`'s coarser test is 2b's to install, and the *soundness* of dropping `k` is stage 1's argument, not something 2a decided.
  - **`rec_ca` compares `(env, syntax)`**, per the handoff: `RecSide` carries `RecCtx` and every motive, branch and branch type is `embed_*_at`'d in the side's own scope. `rec::branch_specs` still takes `&env.gamma`, and reads only its length and base.

  **The bench is the story of this stage.** Four rounds, each ~1.3× and each a *copy*, not an allocation:
  (a) `Nat`/`ze` synthesized per comparison node — interned per thread;
  (b) whnf results cloned on entry and moved by value into the δ stage — `Tm` became `Rc<Term>` (so a whnf and a sub-structure share a representation and `head_tm` is a refcount bump), and the whnf forms are threaded by `&mut`;
  (c) the *root* of a conversion wrapped in an `Rc` — hence `whnf_ty_root`/`whnf_tm_root`, which reduce the caller's borrow in place. At values these are evaluation in the identity environment, which is what §3.2 says a root is anyway;
  (d) `match (view(a), view(b))` building a **tuple of views** — two 40-byte copies per node, 60% of `ty_nf`'s time. Fixed by binding each view to a local and matching `(&va, &vb)`, which also makes the children bind as `&D::TyC` — exactly what the judgments take. Final state: `nat/check-numeral` 4.83 → 5.34 µs at 64 levels (1.10×, inside the harness's band), everything else at baseline.

  Asymmetry worth knowing: at `Syn`, `Ty = Type` but `Tm = Rc<Term>`. Types are what the root API lends us by reference; terms are what the neutral judgments pass around twice.

  **What 2b must know.**

  - **`Env` is the seam that did not move.** Γ is still a syntactic `LocalCtx`. Its entry *types* are read in exactly one place (`Dom::var_type`); everything else — `LocalSubst::id` inside `inst_ty`, `wf_step_telescope`, `rec::branch_specs`, `inst_*_motive` — reads only its **length and base**. So 2b widens `Env` with ρ and value-typed entries and can leave a length-and-base carrier where Γ is; it does not have to make those three telescope helpers value-aware. `push_entry` and `push_spec` are the two methods that will need real work, because at values pushing a binder also extends ρ with the binder's fresh neutral.
  - **`wf_step_telescope` is the one method with no value implementation in sight.** It is handed `shape`, `arity`, `motive` as domain objects and returns three types; at `Syn` it is `term.rs`'s shared function verbatim, at values it must be rebuilt from `Dom`'s own constructors (`wf`, `vec`, `pi`, `fin`, `nth`). Everything else in `tm_ne` is already expressed in operations the value domain has.
  - **`TyC` at values cannot be just `Rc<TyClo>`.** `Dom::el` builds `El^l s` where `s` is a domain term, and `Dom::pi`/`vec`/`w`/`sum`/`id` build formers whose children are domain objects; none of those can be an environment-plus-syntax closure. Either `TyClo` gains a `Val(Rc<VTy>)` case or `TyC` becomes a small enum over "closure | value". Same for the `Vec` length, which `VTy::Vec` stores already forced as `Rc<Val>` while the view wants a `TmC`.
  - `value.rs` and `eval.rs` were **not modified**: the trait was designed against them but nothing here calls them.
  - The stage landed as one commit rather than one per former group. The `Conv<D>` signature change is atomic — every judgment is mutually recursive with every other — so a per-group sequence would have needed a syntax escape hatch whose own removal is the risk the staging was meant to avoid.
