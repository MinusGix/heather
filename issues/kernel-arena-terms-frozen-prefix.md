---
title: Arena-indexed kernel terms over a frozen prefix: one representation for the allocation constant and parallel checking
status: open
labels: [kernel,representation,performance,parallelism,design,conversion,evaluator]
area: kernel
created: 2026-09-11
updated: 2026-11-10
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
- 2026-09-13: Design pass landed: docs/kernel-arena-terms-design.md (items 2-6, sized diff per kernel file, prototype slice, decision). Measured on furnace-bb0218be4a (AMD EPYC 9J14) at tree af00689, same instance for every number (scripts/bench --save fresh on the box; certificate warm, release, --features value-metrics, W=1).

DECISION: rewrite LATER, behind a named trigger; take the value-arena slice now.

(1) The parallelism motivation is spent. [[parallel-kernel-gate]] landed Arc-by-alias plus a deferred gate and measured total CPU flat to +-5% across W in {1,2,4,8}; the issue's "sharing a prefix across threads is a data race on the refcounts" was true of Rc and is false of Arc. The arena is not the road to parallel checking. Item 4 (publication/relocation) exists only because of parallelism and therefore is not a cost of the rewrite as now motivated: in a serial kernel the worker IS the parent and there is no rebase.

(2) Item 2's uniqueness half is essentially empty, and the issue guessed wrong about it: subst.rs has no make_mut/get_mut/try_unwrap at all - what it has is shared_ty/shared_tm (subst.rs:271,282), a rebuild-then-drop refcount pair, which is [[subst-rebuild-then-discard]]'s. Live make_mut in the kernel is exactly two sites, both Psi's copy-on-write spine (term.rs:1556, 1566). The identity half is real but mostly value-domain or a generation token; the term half is 8 sites. Every pointer-keyed cache already carries a hand-written retention argument (bounds.rs:101, value.rs:253, program.rs:78, algebra.rs:185) that an append-only arena would replace with a property of the representation - the one place the rewrite makes the trusted base simpler.

(3) Item 2's hard entry is fmt.rs, not subst.rs. write_exact is used as a content identity (elab determinism hashes), and an indexed Term is a u32 that cannot print itself; the note picks the explicit Printed(&arena, id) wrapper over a thread-local arena and says why.

(4) Item 3 decided: COPY, do not hash-cons - and the premise that would have argued for interning is false. std's ArcEqIdent specialization (alloc/src/sync.rs:3549) makes Arc<T: Eq> test ptr::eq first at the root and at every child, so typing.rs:678's 2.78 M-hit `expected == inferred` already stops at a shared subtree. Filed separately as [[kernel-syntactic-eq-relies-on-arc-specialization]]: the shortcut is load-bearing, undocumented, and silently lost by any other handle.

(5) Item 5 sized: ~1 200 kernel-term construction sites in crates/elab (461 literal Rc::new(Term::/Type::), the rest under a local name), 297 Rc<Term>/Rc<Type> signature occurrences, 48 files, concentrated in vec.rs 282 / forded.rs 231 / lgg.rs 134 / inductive.rs 130. One commit; no incremental lane.

(6) Item 6: the adequacy paragraph is drafted in the note's section 6.3, ready to move into DESIGN.md if the rewrite is taken. Per-file diff estimate: kernel ~5 000 lines (term.rs ~900, rec.rs ~800, fmt.rs ~650 rewritten whole, reduce.rs ~600, conv/dom.rs ~500, ...), elab ~2 500, total ~8 000 lines in the trusted base.

PROTOTYPE SLICE (the issue's guess, confirmed and sized): arena-resident forced values. Rc<Val<'v>>/Rc<VTy<'v>>/Rc<VNeutral<'v>> -> &'v Val/&'v VTy/&'v VNeutral, three more arenas on ValueArena. 21 non-test construction sites, 94 type occurrences, six kernel files, ~350-550 lines; every site already has an arena handle in scope. It addresses ~1.94 M of the module's ~2.0 M heap allocations. Beaten alternatives: subst.rs's Option-returning traversal (~600-900 lines, acceptance number is micro-families the module does not spend its time in) and the full rewrite. NOT implemented in this round: it changes Eval::force's return type, which crates/elab/src/certgen.rs:3039 mirrors, so it is outside this round's "no elaborator API change" charter - and it has an owner, [[value-cache-memo-in-arena]], whose four falsifiers (note section 5.3: monotone memory, eviction semantics, the never-memoize-a-failure rule, a negative control) are the work.

K1 ORDERING, for the coordinator: [[kernel-native-bitvector-values]] is a Val constructor. Val/VTy already borrow the query region; nothing in K1's adequacy argument, native fold or differential oracle mentions how a Term child is spelled. K1 never depended on this issue and is unblocked now. The only real interaction runs the other way: the slice above rewrites Val/VTy ownership, so a K1 variant written first gets rewritten by it.

TRIGGER for taking the term rewrite: after the slice and K1 land, a profile attributing >=15% of kernel wall to malloc/free/refcount traffic over Term/Type nodes specifically (not values, not closures), or a workload needing intra-module parallel checking at a width where Arc contention is measurably non-flat (today flat to +-5% at W=8). Explicitly NOT reasons: parallel checking, and hash-consing's conversion shortcut.

BEFORE COLUMN, this box, this tree (note section 2): certificate warm, release --features value-metrics, W=1 — wall 42.66 s, user 42.17 s, peak RSS 928.4 MB; certificate module total 36.89 s, kernel_gate 26.66 s over 3 476 items; 16.07 M eval steps, 237 888 conv misses, 6.62 M shortcut hits. term_cache 11 728 592 lookups / 1 374 944 hits; type_cache 12 748 766 / 163 309. Lookups-minus-hits = 22 938 105 Rc<Val>/Rc<VTy> heap allocations for ONE certificate build — the five-node module's 1.94 M is the same quantity an order of magnitude down, so the slice's before column should be the certificate, not that module. scripts/bench --save fresh on the same instance; every slope inside its band (nat/step-once 157 ns, step-into-closed-body 175 ns, add-normalize@1024 240.94 us slope 1.00, mul-normalize@48 483.45 us slope 1.95, conv/computed-numeral@512 403.37 us, check/generated-terms@200 5.12 ms, stack 1 530 levels).

SURPRISE, filed not exploited: the type memo answers 1.3% of its lookups (163 k of 12.7 M) — every other lookup pays a probe, a force, an allocation and an insert. [[type-value-memo-hit-rate]]; its four rates should be recorded before the arena slice makes the counter stop meaning "allocations".
- 2026-10-30: The design pass's prototype slice landed (arena-resident Val/VTy/VNeutral plus the value-domain Elim cells): kernel gate −18 to −23% on the cloud box, peak RSS unchanged. Before/after in [[value-cache-memo-in-arena]] (closed).
- 2026-11-02: Trigger check from the data-oriented survey (2026-11-02, `docs/data-oriented-survey.md` §8). In cold gdb-sampled checks, 32–42% of samples have an allocator frame on top. Most of that is elaborator-side copying of non-term data ([[elab-probe-clone-copies-attempt]], [[elab-cx-persistent-binders]]), so the ≥15% Term/Type trigger has not fired. Re-read it once those two land. [[kernel-compact-level]] (Term 128 → ~80 B) and [[subst-per-call-allocations]] are the representation-preserving steps that shrink the term share without the rewrite.
- 2026-11-02: 2026-11-02: [[kernel-compact-level]] landed: a 16-byte canonical Level, Term 128 → 104 B, Type 72 → 56 B; cold calc_parser max RSS −10%, gate −6.8% (perf ab). The 8-byte step, which needs an interned join table, is [[kernel-level-eight-bytes]]. An arena would give it that table for free.
- 2026-11-05: gardener: cites a file it shares with [[frontend-roadmap]] (`crates/elab/src/certgen.rs`); [[resolver-lookup-constant]] (`docs/data-oriented-survey.md`).
- 2026-11-10: [[kernel-level-eight-bytes]] landed without an arena: a process-wide join table that the showcase and the x86 certificate leave empty, so an arena-scoped interner is no longer something this design would be buying.
