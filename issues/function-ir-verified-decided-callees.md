---
title: Compile calls of functions whose tests go through a connective or a Bool helper
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-24
updated: 2026-10-24
---

B2's first step taught the program reflector (`function_ir_source/program.rs`)
`||`, `&&`, `!` and Bool helpers of words: each becomes a tree of
`Conditional`s on plain comparisons, and the certificate proves agreement
through an *expansion*, the same tree spelled in source operations:
`program_eval = expansion` by `refl`, then `expansion = source` by
`split_all; all_goals { refl }`. A function like that "decides".

A call **of** a deciding function is refused. The caller's agreement is by
`refl` (or through its own expansion), and both unfold the callee's source,
whose `match` on `a || b` has no commuting conversion with the IR's nested
conditionals, so neither route closes. The refusal names this issue.

## The ideal shape

Agreement per function, composed at calls: one theorem per callee,
`program_eval(P, g, args) = g_source(args)`, and a call rule for
`program_eval` (evaluating a `Call` node is evaluating the callee's region
on the arguments) so the caller's proof rewrites each call with the
callee's theorem instead of unfolding it. The caller's own `refl` (or
`split_all`) then only sees its own body. This also takes the agreement
cost from the size of the whole call tree down to each function, which
[[function-ir-verified-compile-cost]] wants anyway.

What is not the fix: inlining callees' expansions into the caller's
expansion. It works, but every caller re-proves its callees, and the
expansion grows with the call tree.
