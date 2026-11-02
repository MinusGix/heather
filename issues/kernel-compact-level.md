---
title: A compact, canonical Level: 24-byte Arc trees size every Term at 128 bytes
status: open
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
