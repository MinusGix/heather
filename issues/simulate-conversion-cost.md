---
title: Discharging simulate by conversion costs ~2s per executed step
status: open
labels: [kernel,elab,performance,ir]
created: 2026-07-31
updated: 2026-07-31
---

Found while landing lib/ir_v1.hthr ([[ir-simulate-design]]): running the IR
interpreter under conversion costs roughly **1.5–2 seconds per executed
fuel step** (release build, 2026-07-31). A ~20-step `add(2,3)` certificate
takes ~40s; the design doc's target of "realistic program size and fuel" is
orders of magnitude away. This is the doc §5 cost-model warning confirmed
empirically, before the bench fixture even exists.

## Measurements (chain of 5 LetCons + Ret at fuel 9, one theorem)

| interpreter | time |
| --- | --- |
| 2-constructor Ir, small eval body | 0.24s |
| 8-constructor Ir, arms mostly `Stuck` | 1.2s |
| 8-constructor Ir, + `eval(k, prog)` in 4 untaken arms | 2.3s |
| 8-constructor Ir, full arm bodies (any factoring) | 12–15s |

Factoring the interpreter into step_* helpers, or through a single
dispatch, does NOT help beyond keeping the ih single-occurrence — because
the elaborator **inlines every `fn` at every use** (crates/elab/src/lib.rs:12),
so the kernel term contains the whole interpreter at every call site, and
each fuel-step unfolding substitutes into (and walks) the entire body.

## Two compounding causes, both already known in other forms

1. **No definitions in the kernel term language**: `fn` is inlined at use,
   so a self-call's induction-hypothesis term carries the full eliminator
   with the full body inline. Every syntactic occurrence of the self-call
   costs ~50ms per step (measured: +1.1s over 5 steps for 4 extra
   occurrences). Ψ-globals exist and theorems already live there — whether
   computing `fn`s could be Ψ-referenced rather than inlined (delta
   unfolding at conversion) is the structural question this issue owns.
2. **Substitution still walks closed subtrees** ([[subst-visits-closed-subtrees]]):
   each step's β-substitutions traverse the whole inlined interpreter even
   though nearly all of it is closed.

## Consequences while open

- lib/ir_v1.hthr keeps its acceptance theorems to ONE full-pipeline
  positive and small negatives; its comments cite this issue.
- The [[ir-simulate-design]] §11 bench fixture ("realistic size and fuel")
  is blocked in spirit: it can be written, but the numbers it reports will
  measure this issue, which is arguably its job.
- The surface discipline that emerged (single ih occurrence via a dispatch
  function) is worth keeping regardless: it is the difference between the
  12–15s row and multi-minute rows at higher fuel.

Not currency here: the IR encoding's size per se (spec objects are off the
runtime ledger, [[datarepr-separation]]) — the cost above is per *kernel
conversion* step, which is exactly the ledger `equiv` discharge lives on.

## The delam reading (2026-07-31): definitions are an extension we would own

Read for whether the book's Ψ has a definitional-bindings story to extend.
It does not, and the *reason* it does not is the design constraint:

1. **No bodies anywhere.** Ch. 04's global-binding grammar (line ~808) is
   exactly `g : Ctx | U : DTyp i l | u : DTrm i T l` — declarations only.
   `letbox` is code *composition*: it substitutes eagerly and leaves
   nothing resident. Nothing to extend; a bodied binding is a new former
   with the full ch. 04–07 bill, like the Σ/Id/Wf extensions before it
   ([[metatheory-ch07-pass]] is the precedent and the template).
2. **Intensional analysis already treats globals as syntax.** Ch. 06
   blocks the code-recursion principles on global variables (line ~40),
   compares boxed globals *syntactically* (line ~650), and the recursor
   has a dedicated `u`-branch. So a bodied `u` that conversion unfolds
   would let code-level conversion identify `box(u)` with `box(body)`
   while the recursor distinguishes them — breaking coherence. The design
   consequence is forced, and it is pleasingly DeLaM-shaped:
   **layer-indexed transparency**. Definitions unfold at layer p (running
   is prog's business) and stay opaque neutrals at layer c (code is
   syntax). That is the run/inspect split the layers already encode —
   and it is independently *wanted*: `.code` carrying stable `u`-refs
   instead of inlined bodies is better for intensional instance keying
   ([[compile-typeclass-design]]).
3. **Ch. 07 bill**: the logical relation interprets a bodied `u` at p by
   its body (definitional glueing, standard) and at c as a neutral — the
   fundamental theorem's `u`-cases redo under the split. Real work,
   existing shape.

**Ordering consequence.** The reading also demoted this from "next" to
"second": the fixture pair (`conv/simulate-payload`, slope 0.91) shows the
dominant near-term cost is substitution *visiting* closed subtrees to
discover they're shareable — and [[subst-visits-closed-subtrees]] is a
pure implementation round (per-node free-variable bounds), no book
contact, whose success criterion is literally that fixture's slope going
toward 0. Do that first; the definitions round then buys what metadata
cannot — term *size* (statements, ih copies), `.code` stability, and the
spine costs — with the design above as its charter.

## Log

- 2026-07-31: Superlinearity measured while sizing lib/ir_v1.hthr's acceptance: cost is not linear in executed steps. Same interpreter, same file, release build: ~10 steps (add zero-iteration) 23s; ~16 steps (add(1,1), one loop iteration) 66s; ~22 steps (add(2,3) through LetCall) exceeds 300s CPU. Per-step cost grows with depth -- consistent with the working term growing as evaluation proceeds while substitution walks the whole (inlined) body each step. Consequence applied: the library certifies the loop and the call on separate short paths, and the cargo-test acceptance is #[ignore]d (debug profile is a further ~10x: decls alone 1.1s release vs 11.8s debug), with release heather check as the routine gate. Fixing this issue is what un-ignores that test.
- 2026-07-31: Route (1) priced: it is a KERNEL round, not an elaborator switch. GlobalBinding::Tm carries no body (typed opaque constant); reduce.rs:1956 treats GlobalTm as neutral and conv.rs:1000 compares by variable -- there is no definition/delta mechanism anywhere in the kernel. Definitions-with-bodies + delta unfolding in whnf/conversion (plus an unfold heuristic for f(x) vs f(y)) is a new kernel feature with a ch. 04-06 metatheory obligation; check docs/delam first for whether the book's Psi has a definitional-bindings story to extend rather than invent.
- 2026-07-31: Delam reading done (body section above): no definitional bindings in the book to extend -- bodied globals are a new-former-grade extension; ch. 06 blocks code recursion on globals and compares boxed globals syntactically, so transparency must be layer-indexed (unfold at p, neutral at c). Bench fixtures landed (conv/simulate-payload slope 0.91, conv/simulate-depth 0.97): the payload family is subst-visits-closed-subtrees' acceptance instrument, and that implementation round is now sequenced FIRST, definitions second.
