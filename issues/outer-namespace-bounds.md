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
