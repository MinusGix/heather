---
title: Discharging simulate by conversion costs ~2s per executed step
status: open
labels: [kernel,elab,performance,ir]
created: 2026-07-31
updated: 2026-07-31
---

Found while landing lib/ir_v1.hthr ([[ir-simulate-design]]): running the IR
interpreter under conversion costs roughly **1.5–2 seconds per executed
fuel step** (release build, 2026-07-31). A ~20-step \`add(2,3)\` certificate
takes ~40s; the design doc's target of "realistic program size and fuel" is
orders of magnitude away. This is the doc §5 cost-model warning confirmed
empirically, before the bench fixture even exists.

## Measurements (chain of 5 LetCons + Ret at fuel 9, one theorem)

| interpreter | time |
| --- | --- |
| 2-constructor Ir, small eval body | 0.24s |
| 8-constructor Ir, arms mostly \`Stuck\` | 1.2s |
| 8-constructor Ir, + \`eval(k, prog)\` in 4 untaken arms | 2.3s |
| 8-constructor Ir, full arm bodies (any factoring) | 12–15s |

Factoring the interpreter into step_* helpers, or through a single
dispatch, does NOT help beyond keeping the ih single-occurrence — because
the elaborator **inlines every \`fn\` at every use** (crates/elab/src/lib.rs:12),
so the kernel term contains the whole interpreter at every call site, and
each fuel-step unfolding substitutes into (and walks) the entire body.

## Two compounding causes, both already known in other forms

1. **No definitions in the kernel term language**: \`fn\` is inlined at use,
   so a self-call's induction-hypothesis term carries the full eliminator
   with the full body inline. Every syntactic occurrence of the self-call
   costs ~50ms per step (measured: +1.1s over 5 steps for 4 extra
   occurrences). Ψ-globals exist and theorems already live there — whether
   computing \`fn\`s could be Ψ-referenced rather than inlined (delta
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
conversion* step, which is exactly the ledger \`equiv\` discharge lives on.

## Log

- 2026-07-31: Superlinearity measured while sizing lib/ir_v1.hthr's acceptance: cost is not linear in executed steps. Same interpreter, same file, release build: ~10 steps (add zero-iteration) 23s; ~16 steps (add(1,1), one loop iteration) 66s; ~22 steps (add(2,3) through LetCall) exceeds 300s CPU. Per-step cost grows with depth -- consistent with the working term growing as evaluation proceeds while substitution walks the whole (inlined) body each step. Consequence applied: the library certifies the loop and the call on separate short paths, and the cargo-test acceptance is #[ignore]d (debug profile is a further ~10x: decls alone 1.1s release vs 11.8s debug), with release heather check as the routine gate. Fixing this issue is what un-ignores that test.
