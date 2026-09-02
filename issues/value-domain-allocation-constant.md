---
title: The value domain costs a 1.5-3x constant where there is no sharing to win
status: open
labels: [kernel,conversion,performance]
created: 2026-07-31
updated: 2026-09-02
---

Stage 2b of [[nbe-conversion-round]] killed the exponential (the acceptance
instrument went 33.77 s → 1.87 s at N = 15 and flat) and paid a **constant**
for it. `scripts/bench --check` was re-recorded at that commit; the numbers
against the pre-stage baseline were:

| family | ratio | what it is |
|---|---|---|
| `conv/computed-numeral` | 3.2× | `add n n ≈ 2n` — pure computation, zero reuse |
| `conv/simulate-depth` | 2.5× | the interpreter shape at fixed payload |
| `conv/simulate-payload` | 2.3× | same, at fixed fuel (flat, as its band requires) |
| `wf/check-tree` | 1.9× | `Vec`/`Fin` unfolding per constructor |
| `conv/perturbed-pairs` | 1.5× | the property-test corpus |
| `check/generated-terms:50` | 1.27× | checker throughput |
| `wf/mirror-involution` | **0.30–0.40×** | two eliminations over one tree — sharing |
| routine `lib/ir_v1.hthr` | **recovered** (1.28 s → 1.57 s → 1.26 s) | see below |

The user-visible one came back on its own. Two fixes at the end of the stage
— sharing Ψ instead of cloning it (and its bindings' local contexts) at every
binder push, and indexing identity environments by length instead of walking
back from the longest — put the routine check at **1.26 s**, under its
pre-stage 1.28 s. They did nothing for the table's first six rows, and the
reason is worth keeping: those fixtures run over an empty Ψ and an empty Γ,
so there was no scope there to stop copying. What is left is the allocation
below.

**No slope moved and no declared band was left**, so this is a constant
factor and not a change in the cost model. Two rounds of it were already
clawed back during 2b (materializing the value scope per query cost O(|Γ|)
allocations; the two roots wrapped syntax they had only borrowed), which is
what brought `nat/check-numeral` and `check/generated-terms:25` back under
threshold.

**Diagnosis, from `perf record` on `conv/simulate-*`:** ~20% of the profile is
`malloc` / `cfree` / `Rc::drop_slow`, plus `eval::tclo` + `eval::yclo` at ~5%.
A lazy sub-structure is an allocation (`Rc<TmClo>` or `Rc<TyClo>`, one per
child of every node evaluated) where the rewriter had an `Rc::clone` of a
subterm it could share outright. On terms with no reuse that allocation is
pure loss; it is the price of the laziness that makes the never-forced
induction hypothesis free, which is the whole round.

Not levers, and why (the issue's own rule 3 — this file is a measurement, not
an optimization plan):

- *Strict children.* Would delete the allocation and re-introduce the defect:
  design §12's family C is exactly a never-forced ih.
- *Skipping the memo cell.* `RefCell<Option<_>>` is 2 words inside an
  allocation that exists anyway.

Worth trying, in rough order of expected yield:

1. **An arena or a free-list for `TmClo`/`TyClo`.** These are allocated and
   dropped in tight waves within one conversion query, which is exactly the
   shape a bump allocator serves. The kernel is zero-dependency, so this is a
   hand-rolled pool, and `Rc` makes lifetimes the hard part.
2. **Inline the one-binder closure.** `TyClo::Syn { env, body }` where `env`
   is `ρ.push(one value)` is the commonest shape `open_*` builds; a
   `Clo1(parent, arg, body)` case would save the `EnvNode` allocation.
3. **A frame stack that outlives one `Eval`.** `Eval::drive` reuses its
   continuation stack, but `conv/dom/values.rs` builds a fresh `Eval` per
   `Dom` operation, so the reuse never spans two. Threading one buffer
   through `Conv` would make it real.
4. **Do not re-wrap a whnf value as a carrier.** `TmC::value` allocates a
   `TmClo` around a `Val` the caller already has; the neutral views do this
   once per spine node.

**Trigger:** any round that finds a workload where the constant outweighs what the
exponent bought. Stage 4 of [[nbe-conversion-round]] re-measures `bounds.rs`
and should re-read this at the same time — conversion no longer calls
`apply_local` at all, so the two questions share a profile.

## Log

- 2026-08-01: Attribution datum from the release `heather check lib/ir_v1.hthr`
  profile (~34s, fp call-graph): allocator time (malloc 4.9% + cfree 5.0% +
  libc internals ~4% + `Rc<VTy>`/`Rc<TyClo>` drop_slow ~5% + Level/Type drop
  glue ~3.6%) is the largest block of the run, ~18-20% combined. Immediate
  callers of malloc, by sample count: `Values::push_entry` 85,
  `Eval::eval_ty` 79, `open_ty` 67, `Eval::force_ty` 55, `value::Env::extend`
  38 — i.e. exactly the closure-allocation shape this file diagnosed on
  `conv/simulate-*`, now confirmed on the real library at 20x the scale.
  The "worth trying" list is unchanged by this datum; items 2 (Clo1 inline —
  `open_ty`/`push_entry` are top callers) and 4 (`TmC::value` re-wrap) look
  like the contained first bites. Ranked against [[context-representation-clones]]'
  Gamma half (~8%) this block is bigger but spread across more edits.
- 2026-08-14: Verdict from [[conversion-cost-at-large-values]]'s round (closed),
  which this file's body asked for: the large-canonical-value conversion cost
  did **not** decompose into this constant except at the margin. ~97% of the
  reproducer's `conv_type` calls compared syntactically equal inputs —
  reflexivity paid at full structural price, i.e. this constant multiplied by
  a walk that did not need to happen — and a syntactic-reflexivity
  short-circuit (root `==`; same-env/equal-body closure fast path) removed it
  without touching allocation at all. What that round leaves behind and hands
  to this file: the genuinely-different comparisons (~0.55 s of the
  k_bind_mono reproducer's remaining 0.62 s of conv), whose per-node price IS
  this constant. The "worth trying" list above is unchanged and is the lever
  if that residual ever triggers a round.
- 2026-08-26: ITEM 1 (arena) landed for a stronger reason than allocator
  throughput: recursive destruction of a successfully forced machine-width
  graph overflowed the native stack, and unbounded/weak per-node memos then
  exceeded the 4 GiB rail. Query-local typed arenas plus bounded 16K FIFO
  caches fix both failure modes, but the benchmark exposes a new constant:
  the bounded cache is a pointer-keyed `HashMap`, so every force hashes where
  the old thunk read its own memo cell. Against the pre-arena recorded
  baseline, no slope moves, but no-sharing value families are about 1.3--1.5x
  slower and `nat/check-numeral` is about 2.2--2.5x slower because it opens
  many tiny conversion queries. This was reproduced after evaluator metrics
  were compile-time-gated completely out of the ordinary build, so counters
  are not the cause. A direct cache-slot index (`Cell<Option<…>>`) on each
  arena closure was implemented as the first probe and reverted: it removed
  hashing and let eviction clear/reuse slots safely, but enlarging every
  closure made `nat/check-numeral` worse (about 2.4x became 2.4--3.9x, with
  the smallest queries hurt most). The next representation must avoid a word
  on every closure as well as a hash on every force. A small-query no-cache
  policy is a possible probe, not a design: the metrics show workloads differ
  sharply, and silently discarding sharing based on query size can merely move
  the cliff. The arena solves a correctness failure and remains landed; the
  baseline is re-recorded as required, with the regression and mechanism
  explicitly owned here rather than silently normalized away.
- 2026-09-02: A generated FunctionIR/x86 scaling profile fired this issue
  again at a much larger real workload. At five ALU nodes the checker built
  about 27.5 M environment cells, 25.1 M term closures and 48.4 M type
  closures; `perf` was allocator/cache/destructor topped (`malloc` 6.4%,
  `ValueArena::cache_ty` 4.4%, `Vec<Elim>::clone` 2.1%, with further free,
  `Rc` and arena-drop cost). The first representation fix landed here:
  neutral elimination spines are now persistent arena lists. Extending a
  neutral and viewing its immediate predecessor are O(1), replacing two full
  `Vec<Elim>` copies, with no per-node heap allocation or recursive drop.
  On the generated 20-node module this moved 105.6 s to 84.7 s (~20%); the
  application-heavy `gprs_congruent` item moved from ~9.0 s to 6.2 s at 20
  nodes and 2.4 s at the five-node diagnostic size. The kernel rails and a
  100k-cell non-recursive spine regression pass.

  Two negative probes constrain the next step. A 64-slot allocation-free
  exact interner for `(Rc<Type>, Env)` syntax closures found only 1,718 hits
  in 46.3 M constructions (0.0037%) and was reverted: these are genuinely
  changing closures, not locally lost pointer identity. Enlarging the
  bounded type cache from 16K to 64K gained only ~180K hits while 16.3 M
  evictions remained and wall time regressed, also reverted. The remaining
  target is therefore the production of changing environments/closures (or
  a representation that makes their changes virtual), not a larger table.

  The post-fix `perf` sample confirms `Vec<Elim>::clone` disappeared. The
  residual remains allocator/cache dominated: `_int_malloc` 6.1%,
  `cache_ty` 4.7%, allocator consolidation/unlink 7.6% together, and value
  cache hashing about 3%. A deterministic mixed-pointer hasher plus one-probe
  insertion looked locally obvious but failed the real gate: the generated
  process ran beyond twice its prior completion time and was stopped. Both
  changes were reverted. Do not replace hashbrown's hasher from a flat
  instruction profile alone; bucket/probe behavior and the full memory rail
  are part of this cache's acceptance test. A cache redesign should instead
  address admission and closure production together.

- 2026-09-02: The next environment-representation probes separated retained
  size from the tempting source-level story. An arena environment cell used
  to contain its captured value plus an entire `Env` tail (32 bytes): the
  arena pointer and length were therefore repeated at every link. Making the
  cell a plain `(value, next-cell)` pair cuts it to 16 bytes while preserving
  the 24-byte, copyable `Env { arena, head, len }` handle and all lookup/
  prefix semantics. On the generated 20-node FunctionIR module the first
  run moved 84.7 s to 82.2 s; that small wall-time change is within machine
  noise, but the structural saving applies to all 27.2 M cells observed by
  the five-node allocation instrument (about 435 MiB of cell storage rather
  than 870 MiB).

  Two more aggressive forms were implemented as probes and rejected. A
  stack-local virtual `Push1Env` avoided materializing only 357 of
  27,170,490 cells (0.0013%): dependent closure construction almost always
  captures the extended environment before returning, so the virtual view
  immediately has to become persistent. Moving `len` into each node made
  `Env` and `TmClo` eight bytes smaller, but made every cell eight bytes
  larger and did not shrink `TyClo` at all (its uncommon inline `Level`
  payloads determine that enum's size). At the measured allocation mix this
  is roughly 200 MiB saved in term closures versus 216 MiB added in cells,
  before allocator effects, so it was not retained. A future compact handle
  must remove its arena pointer while keeping 16-byte cells, which means
  threading the already-known query arena through extension; shrinking
  `TyClo` additionally requires moving the uncommon synthesized level-bearing
  cases out of line. Those changes should land together and earn their larger
  trusted-kernel surface with a fresh whole-workload measurement.
