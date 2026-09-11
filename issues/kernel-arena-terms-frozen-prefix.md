---
title: Arena-indexed kernel terms over a frozen prefix: one representation for the allocation constant and parallel checking
status: open
labels: [kernel,representation,performance,parallelism,design,conversion,evaluator]
created: 2026-09-11
updated: 2026-09-11
---

Evaluate replacing the kernel's `Rc`-owned term trees with arena-indexed terms over a frozen prefix, so that (a) the value-domain and term allocation constant goes away at the representation level rather than one pool at a time, and (b) independent declarations of one module can be kernel-checked in parallel without atomic reference counts.

## Why now

Two measured walls point at the same representation (2026-09-11):

- **Allocation.** ~1.94 M `Rc` memo allocations against ~60 k arena chunks per five-node x86 module, a ~30% allocator share of module wall ([[value-cache-memo-in-arena]], [[value-domain-allocation-constant]]); the closed [[conversion-query-arena-pooling]] refused pooling by measurement because the `Rc`s beside the arena are what allocate.
- **Parallelism.** The `reused_callee` certificate is 3 474 generated theorems, none over a second, all successful, kernel-bound at ~1.7 M evaluator steps/s, 86 s of 128 s ([[function-ir-x86-proof-scaling]] log 2026-09-11). The dependency graph is wide and shallow. Nothing in the kernel can check two of them at once: every `Term`/`Type` child is an `Rc`, and a worker that evaluates against a shared prefix clones those, so sharing a prefix across threads is a data race on the refcounts. "Views" over `Rc` terms therefore do not exist as a halfway design; they exist only once terms are indices.

Decision recorded (user, 2026-09-11): the utility justifies a representation rewrite of the trusted base before Heather-in-Heather can verify it — we are hitting the limits first. The [[kernel-acceleration-policy]] stance (representations with adequacy arguments, not shape cases) is the frame this must satisfy.

## The idea

- The committed prefix (Ψ and every term it owns) is **frozen**: an append-only arena shared by `&'p Arena`. Ψ already has this shape — sealed chunks plus a tail behind one identity (`term.rs::GlobalBindings`) — and the value domain already lives in a lifetime-borrowed `ValueArena<'v>`. What does not is `Term`/`Type` themselves (226 `Rc<…>` sites in `term.rs`, ~2 800 kernel-wide).
- A **sub-kernel** is a worker holding `&'p Arena` plus its own local arena. Ids below the split resolve to the prefix, ids above to local nodes. It evaluates and checks one declaration (or a batch), returns a verdict and, if the declaration lands, the nodes it needs to publish. The parent appends those to the prefix once every worker of the batch has returned; the next batch sees the longer frozen prefix.
- No reference counts anywhere on the hot path: cloning a term is copying a `u32`. Sharing is free; lifetimes carry the frozen/local distinction; the borrow checker enforces that a worker cannot mutate the prefix.

## What has to be evaluated before committing

1. **The Arc tax, as the control.** `use std::sync::Arc as Rc` compiles workspace-wide with no other change; measure it on `scripts/bench` (same box, `--save` then `--check`) and on the `reused_callee` kernel column. If atomics are cheap uncontended, `Arc` plus a deferred gate is a shorter road to parallel checking, and the arena rewrite is justified by allocation alone; if they are not, the rewrite is the only road to both.
2. **Everything that relies on `Rc` identity or uniqueness:** `Rc::ptr_eq` fast paths, `make_mut`/`get_mut` in `subst.rs`, the bounds memo and any cache keyed by pointer ([[bounds-metadata-taxes-one-shot-checking]]), `BodyCache`, the value-domain closures and `Env` cells, the budget-bounded `Debug` in `fmt.rs` (CLAUDE.md) — each needs its id-based equivalent named.
3. **Substitution and shifting under indices.** Today's `Rc` trees share subtrees implicitly across substitutions; an arena either hash-conses (then equality of ids is a real fast path, and `conv_ty`'s 2.78 M shortcut hits per omega module get cheaper) or copies (then [[open-payload-shift-copies]] returns). Decide which, with the DAG-sharing arguments from [[succinct-inductive-values]] and [[generated-source-semantic-term-sharing]] in view.
4. **Publication cost.** What a worker returns must be relocated into the prefix (ids rebased). This is the relocation problem [[relocatable-semantic-module-images]] already has for on-disk images; the in-memory version should be the same code or the same argument.
5. **The elaborator boundary.** The elaborator constructs kernel terms directly in ~63 files; it needs one construction API (an arena handle) rather than `Rc::new` at each site, which is also what [[elaborator-canonical-type-spelling]]'s "one spelling" chokepoint wants.
6. **Adequacy.** The trusted base's argument today is "the term is the tree"; with indices it is "the term is the tree the arena denotes", which needs the arena to be append-only and ids never reused within a frozen prefix. Write that paragraph for `crates/kernel/DESIGN.md` before writing code.
7. **The serial remainder.** Even with the kernel fully parallel, the elaborator's own time (32 s of the 128 s certificate; the unattributed `other` bucket) stays serial; [[perf-instrumentation-consolidation]] owes the timers that name it, and [[parallel-checking-and-caching]] owns splitting it across processes.

## What it assumes from elsewhere

- **[[parallel-checking-and-caching]]** owns cross-process parallelism and the shared telescope. Assumed here: only that intra-process, intra-module parallel checking is its stated blocker, and that this issue is the representation half of unblocking it.
- **[[value-cache-memo-in-arena]]** owns the next slice of the allocation constant. Assumed here: that its measurement (33:1 `Rc` to arena chunks) is the before-column for the rewrite.

## Acceptance (for the evaluation, not the rewrite)

- The Arc-tax measurement is recorded here with its box and commit.
- A design note (`docs/kernel-arena-terms-design.md`) answers items 2–6 with a sized diff estimate per kernel file, and names the prototype slice (likely: arena-index the value domain's `Rc` memos first, since they are already beside an arena, and measure).
- A decision: rewrite, `Arc` + deferred gate, or forked workers as the interim.

## Log

- 2026-09-11: Arc-tax control measured 2026-09-11 (furnace-bb0218be4a, EPYC 9J14, release, tree c0f7f05 + `use std::sync::Arc as Rc` in every workspace file, no other change; same-box scripts/bench --save baseline under Rc, then --check under Arc; single-threaded, so uncontended atomics only). Kernel bench, Arc/Rc medians over 87 cases: median 1.04x. Refcount-dense micro-steps pay most: nat/step-once 1.28x (128 -> 163 ns), nat/step-into-closed-body 1.24x, nat/add-normalize and mul-normalize 1.20x — the four families --check flags. Conversion and checking families 1.02-1.06x (conv/* 1.03-1.05, wf/* 1.02-1.06, check/generated-terms 1.06, code/* 1.04-1.05); subst and level families within noise (0.84-1.02). Module scale, reused_callee build-x86 warm: wall 128.0 -> 130.5 s, certificate kernel_gate 85.7 -> 87.4 s (+2%), items 117.7 -> 119.9 s. Reading: Arc is affordable as the single-threaded tax — a 2% module-scale cost against an 8-way kernel — but the contention cost of many workers cloning shared prefix nodes is unmeasured and is the number the deferred-gate prototype must produce. Confound to remember: the first Arc run rebuilt the 28 library modules from source (94 s, no decode/recheck rows) because the image cache keys on the compiler binary, so compare warm runs only.
