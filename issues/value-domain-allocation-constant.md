---
title: The value domain costs a 1.5-3x constant where there is no sharing to win
status: open
labels: [kernel,conversion,performance]
created: 2026-07-31
updated: 2026-08-01
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
