---
title: A compact, canonical Level: 24-byte Arc trees size every Term at 128 bytes
status: closed
labels: [kernel,performance,representation]
area: kernel
created: 2026-11-02
updated: 2026-11-02
---

Give `Level` a compact representation, canonical if possible. Today it is 24 bytes with `Arc` children, inline in every annotated node, and it sets `Term` at 128 bytes and `Type` at 72.

## Problem

`enum Level { Var, Zero, Succ(Rc<Level>), Max(Rc<Level>, Rc<Level>), Omega }` (`crates/kernel/src/level.rs` ~23) is 24 bytes. `App` holds two, `Pi` two, `Case` three, and the largest variants (`Case`, `ElimCodeTm`) fix `size_of::<Term>()` at 128 and `Type` at 72 (`term.rs`'s `syntax_nodes_stay_their_size`). An `Arc<Term>` allocation is therefore 144 bytes even for a `Var` leaf.

`Level::succ` allocates per `1+` and `Level::constant(n)` allocates n nodes. `shift`, `subst_at` and `inst_at` rebuild the whole tree even when nothing moves. Every rebuilt annotated node does one or two atomic refcount pairs per non-trivial level. [[level-normalization-allocation]] closed by naming this residue: "drop glue on Level clones inside term construction, which is a term-representation question." Survey: `docs/data-oriented-survey.md` §3. In cold samples, `Level` frames alone are 3–5%; the larger effect is on node size.

## Proposal

- **Step 1, 16 bytes:** `Small { offset: u32, base: var-or-Zero-or-Omega }` or `Big(Arc<LevelNode>)` for `⊔` trees, where `LevelNode` holds the canonical form (`LevelNf`: a constant plus sorted `(var, offset)` pairs). `Term` comes to ~104 bytes and `Type` to ~56.
- **Step 2, 8 bytes:** pack it into a `NonZeroU64` with safe decoding (the kernel has no `unsafe`). `Term` comes to ~80 bytes.
- Keep `Level::Zero` and `Level::Var(v)` usable as they are written today (associated constants and constructors; ~1 000 such uses). Only ~20 sites match `Succ`/`Max` structurally, and they move to a `view()` enum.
- Optionally make levels canonical by construction: `equiv` becomes `==`, and [[fn-statement-level-trees]]' blocker goes away. That round measured that canonicalizing at one emitter doubled conversion misses, because the other side still carried the raw tree. With canonical levels there is no per-emitter spelling left.

## Cost and risk

Trusted base. Level printing (`write_exact`, which the determinism hashes and image identities use) and the image encoding change, so the image format bumps. Canonical-by-construction moves every interface hash once; it is sound because `equiv` is the judgement. Run the 300-seed substitution laws, `scripts/bench --check` (the `level/*` family), and `scripts/perf ab` with counters at widths 1 and 8.

## What it assumes from elsewhere

- **[[kernel-arena-terms-frozen-prefix]]** owns the full term-representation decision. Assumed here: only that the term rewrite is not imminent, so a representation-preserving shrink is worth a round. Under arenas, levels would want the same compact form anyway.
- **[[subst-rebuild-then-discard]]** measures the refcount pairs that a compact level partly removes.

## Log

- 2026-11-02: 2026-11-02: Steps 1 and 3 done, and step 2 split out. `Level` is now a 16-byte enum that is canonical by construction. `Zero`, `Var(ℓ)` and `Omega` are unchanged. `Lift` holds `k + 0` or `k + ℓ` inline (k ≥ 1, fits u32). `Join(Rc<Join>)` holds every other finite level as `LevelNf`'s parts: an optional undominated constant and sorted `(ℓ, n)` pairs. The payload fields are private, so a non-canonical level cannot be built outside `level.rs`. `succ`, `max`, `join` and `constant` are O(1) on the inline forms. `subst_at`, `inst_at` and `shift` return a clone when no variable moves. `equiv` is `==`. The `normalize_levels` pass is gone, and `conv.rs`'s `code_eq` is plain `==`. Sizes: `Term` 128 → 104, `Type` 72 → 56, `Val` 88 → 72, `VTy` 72 → 56, `Elim` 128 → 104.

  Soundness argument (in `level.rs`'s module docs): every judgement on levels (`equiv`, `le`, `well_formed`) is a function of the normal form, because normalization never drops a variable and `ω` poisons both sides. Substitution respects `≈`. Oracle: the old tree type and its `count`/`adjust` are kept as a reference model in `level.rs`'s tests. Over 300 seeds, the tests check that building agrees with the reference normal form, that `==` and `le` agree with the reference both ways, and that `subst_at`, `inst_at` and `shift` commute with building. One deliberate tightening: a level with `ω` inside is now `ω`, so it is `le` only to `ω`. Before, the old `le` said everything was `≤` a non-root ω-poisoned level. `Level::le` has no caller.

  Formats: module images `HTHMOD 0x1d` / `HTHIFC 0x1a`, which encode a level as its parts and decode through `Level::of_parts`. Cache domain strings `iface/3`, `check/3`, `axiom-iface/2`, `statement/2`, `store::FORMAT` 3. The Nat suite golden hash moved. `ch05_06_lemmas::level_equivalent_code_is_convertible` now asserts the `ℓ ↦ ℓ ⊔ ℓ` twin is identical.

  perf ab against master, calc_parser cold, width 1, 5 interleaved samples. Wall −4.3%, kernel gate −6.8%, total −5.1%, max RSS −10.0%. All four separate. Counters moved slightly, which is expected now that equivalent spellings are equal: conv_misses −0.6%, conv_memo_hits −1.3%, conv_shortcut_hits +0.2%, eval_steps +0.3%. Bench: `level/equiv-rebuilt` at 64 variables went from 11.4 µs to 55 ns. That family now measures a slice comparison, and a new `level/join` family measures the canonicalizing merge. Baseline rows re-recorded.

  Step 2 (8 bytes) needs an interned join table, because safe Rust cannot pack a pointer and an integer into one word. Filed as [[kernel-level-eight-bytes]]. Closing.
