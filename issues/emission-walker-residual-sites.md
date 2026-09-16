---
title: The slots the emission walker still lists on the library: route each emitter through emit_ty, or quote the respelled type once
status: open
labels: [elaboration,representation,performance]
created: 2026-09-06
updated: 2026-09-16
---

Filed from [[emission-spelling-chokepoint]]'s round (2026-09-06), which landed
`Elaborator::emit_ty` and the walker (`crates/elab/src/emission_walk.rs`,
docs/annotation-component-respell-design.md §2.5). The walker's first
listing on `lib/ir_v1.hthr`'s closure, after the round's own routings
(`Lam.dom` went from 49 to none), is 214 findings whose slots are recorded
as `WALK_RESIDUE` in `crates/elab/tests/ir_v1.rs` — a regression guard that
only ever shrinks. This issue owns draining it. By slot:

| slot | count | what `emit_ty` would write |
|---|---|---|
| `Snd.snd_ty` / `Fst.fst_ty` / `Fst.snd_ty` / `Snd.fst_ty` | 71 / 35 / 18 / 2 | inline `Wf`/`Σ` lowering ⇒ `El (D#tycode^δ)` |
| `Pair.fst_ty` / `Pair.snd_ty` | 16 / 16 | `El ⌜Unit⌝` ⇒ `Unit`, `El ⌜Σ…⌝` ⇒ the inline Σ (quote residue) |
| `App.dom` / `App.cod` | 13 / 12 | inline `Id`/`El ⌜…⌝` ⇒ decoded and respelled |
| `J.ty` / `J.motive` | 12 / 3 | inline lowering ⇒ reference |
| `ElimNat.motive` / `Case.motive` / `ElimEmpty.motive` | 7 / 4 / 2 | inline lowering ⇒ reference |
| `Refl.ty` | 3 | inline lowering ⇒ reference (generated `refl`s beside a `J`, not expr.rs's) |

First declarations at each: `step_mono`, `step_ret`, `step_let*`,
`loop_refines_rec`, `k_bind_inv`, `k_ret`, `eval`, `no_full_refines`,
`eval_functional`, `refines_trans*`, `gather`, `embed_nat`, `bumps`,
`cong_nat_val`. On the five-node FunctionIR/x86 module the walker lists 578,
all but a handful in the Rust-built `mixed_binary_alu_raw`, and every one
carries an `El ⌜⟦Instruction⟧⌝` quote inside the slot — the quote layer,
[[elaborator-canonical-type-spelling]]'s residue, not this issue's.

## Attributed so far

Two of the projection-chain emitters, found with a three-declaration probe
(a record `R5 { f: Flat, g: T }` over two coded declarations; `r.f`, `r.g`,
and `match r { R5(f, g) => f }` each list `Fst.fst_ty` at depth 1 and
`Fst.snd_ty`/`Snd.snd_ty` at depth 2 with the inline `⟦Flat⟧`/`⟦T⟧` where
`El (Flat#tycode^δ)` exists):

1. **`project_field`'s fallback walk** (`inductive.rs`) *is* routed — it
   seeds `cur_emit` with `emit_ty(record_ty)` — but for a coded record that
   is the whole-type reference, and the components it then reads off
   `whnf(cur_emit)` are the code's decode, i.e. the inline field lowerings,
   which nothing respells again. Fix shape: run each link's `fst`/`snd`
   through `emit_ty` (depth 0 and 1) after the whnf, as `projection` does.
2. **`elab_arm`'s alias projections** (`inductive.rs`, the tier-0 `match`
   arm's `fst(snd^j value)` binders) copy `fst`/`snd` inline; never routed.
   Same fix, same two lines.

The rest need the same attribution first: the `J`/motive families are the
rewrite and eliminator generators (`matching.rs`, `lgg.rs`, `indexed.rs`,
`gendefs.rs`'s definition bodies are *not* walked), the `App`s are schema
emitters outside `apply_explicit`/`apply_implicit`, and the three `Refl`s
ride with a `J`. `Term::Fst {`/`Term::Snd {`/`Term::App {` constructor sites
outside `inductive.rs`/`application.rs` are the list to walk.

## What it assumes from elsewhere

- **[[emission-spelling-chokepoint]]** (closed) owns the mechanism. Assumed
  here: only that `emit_ty` is the one spelling and the walker's `Some` is
  the finding.
- **[[elaborator-canonical-type-spelling]]** owns the quote layer. Assumed
  here: only that quoting the respelled type at `code_of` is its slice, and
  that it removes every `⌜…⌝`-carrying row above without touching a
  consumer.

## When

Triggered: the next sampler row the walker attributes to one of these
slots, or the next time the library test's residue list would have to
*grow*. Each drained family is one `WALK_RESIDUE` entry removed and the
test proving it stays gone; the probe above is the fast-lane reproducer for
rows 1–2.

## Log

- 2026-09-10: Item 1 (`project_field`'s fallback walk) landed by [[unnameable-annotation-occurrences]]'s round (2026-09-10), in the fix shape written here: each link's `fst`/`snd` read off `whnf(cur_emit)` now goes through `emit_ty` (depth 0 and 1). Measured on the x86 fetch certificates rather than the library: the chain met the literal at every `FetchedFrom` instance (numbers on that issue). Item 2 (`elab_arm`'s alias projections) is untouched.
- 2026-09-10: Five-node listing 578 → 260 after [[per-instantiation-type-codes]] (2026-09-10): the Supf shape/arity and the whole Fst/Snd chain are gone; Pair.fst_ty/snd_ty 236 → 120 each, App.cod/dom and ElimNat.motive 20 — all pre-existing slots, the closed boxed literal.
- 2026-09-13: The quote layer's remaining literal had one more site than the walker lists, because it is a definition body and not a slot: `register_ty_code_fn`'s `code_of(template)`. Quoted respelled since 2026-09-13 (docs/record-projection-reference-design.md §9.8); the walker's own listing is unaffected, its slots were already routed.
- 2026-09-16: The quote residue this table lists as not its own has been attributed to an item: `complete_post`'s 5.73 M conversion queries are the quote layer's inline component lowerings (docs/complete-post-attribution-design.md §4). Verification item for the slice: this walker's `WALK_RESIDUE` list may only shrink (design §8 item 4).
- 2026-09-16: Re-list after the quote-layer slice (docs/complete-post-attribution-design.md §10.6): `App.dom`/`App.cod` and `Pair.fst_ty`/`snd_ty` were the slots the raw quote fed, so the five-node residue table above is stale until re-run.
