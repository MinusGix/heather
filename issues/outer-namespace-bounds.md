---
title: Global/universe-namespace operations still walk everything; bounds generalize if asked
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

[[subst-visits-closed-subtrees]] landed skip metadata for the local
namespace only; `ShiftGlobal`/`ShiftUniv`/`SubstGlobal`/`SubstUniv`/
`InstUniv` still visit every node. The close log left this unfiled
"until a profile asks"; filed now as an accumulator per the 2026-07-31
decision to track exploratory perf work as small issues.

Mechanism if taken: an `OuterUse` (global-var bound covering `U^δ`/`u^δ`
vars, ctx bases and tail ctx-vars; universe-var bound over levels) beside
`LocalUse` in `bounds.rs`, with its own compute pass — the scoping
differs from the local pass (global/universe ops descend into boxed code
with the local depth reset, so the two passes cannot share one walk), and
`NormalizeLevels` cannot use var-bounds at all (it rewrites var-free
levels too; it would need an "all levels canonical" bit or stay unskipped).
Skip hooks and debug re-verification generalize as-is.

Trigger: a profile with `map_*::<ShiftGlobal|ShiftUniv|SubstGlobal>` as a
top line on a real workload. Today they are ~1.3% on the worst bench;
the likely first customer is the letbox/code-recursor β path
(`SubstGlobal` payload instantiation over 52-branch bundles), which the
definitions round ([[simulate-conversion-cost]]) will exercise harder.

## Log

- 2026-07-31: First named customer, from the definitions round ([[simulate-conversion-cost]]): reduce::Defs::body rescopes a definition's body with shift_global(v.0 + 1) on EVERY unfold, so a global-namespace traversal is now proportional to body size on the hot conversion path -- the one thing per-unfold cost is linear in that metadata could make O(1) for a global-closed body. Not yet profiled, so the trigger (map_*::<ShiftGlobal> as a top line) is not confirmed fired; the workload to profile is release heather check lib/ir_v1.hthr, now ~2.1s.
- 2026-07-31: The post-definitions profile the last entry asked for is taken (release heather check lib/ir_v1.hthr, ~2.1s): sub_ty::<ShiftGlobal> is 2.6% self; all global/universe-namespace ops together ~5%. Defs::body's per-unfold shift_global is real but not a top line -- trigger NOT fired. Re-check after the Psi-clone round ([[context-representation-clones]]), which owns the actual top line and will change the denominator.
- 2026-07-31: Re-checked after the Psi-clone and level-fast-path rounds, as the last entry asked. On the same workload (release heather check lib/ir_v1.hthr, now 1.305s) the ShiftGlobal family is the largest substitution block: sub_ty::<ShiftGlobal> 4.5% self, map_type::<ShiftGlobal> 2.3%, its Mapper::level 0.8% -- ~7.6% for ShiftGlobal alone, with SubstGlobal adding ~1.0%. That is up from 2.6%/~5% mostly because the denominator shrank by 38%, but Defs::body's per-unfold shift_global is now visibly the top substitution cost on the conversion path. The trigger (map_*::<ShiftGlobal|ShiftUniv|SubstGlobal> a top line on a real workload) reads as FIRED; the named first customer from the earlier entry is the one to size.
