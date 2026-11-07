---
title: Check FunctionIR evaluability in one pass, not per nesting level
status: closed
labels: [native, function-ir, perf]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-07
updated: 2026-11-07
---

`StructuredRegion::evaluable` (`lib/native/function_ir/function_ir_eval.hthr`)
recomputes `continuation.writes()` and `prefix.mentions()` at every `Compose`
and `Sequence` level and compares them pairwise (`disjoint`), and
`nodes_evaluable` does the same along a node list. A function lowered from a
runtime fn of nested `match`es is a deep chain, so the check is quadratic in
the nesting depth. The x86 certificate checks it for the whole program in
one declaration (`<f>_native_evaluable`: `program_evaluable(…).IsTrue()` by
`trivial`, generated in `crates/cli/src/native/verified.rs`), against the
kernel's per-declaration fuel.

Found by [[runtime-fn-caller-agreement-fuel]], which took `evaluable` out of
`f::agrees` (linking needs only `calls_fit`). With that done, `compile-x86`
of the self-hosted lexer's `step` (`self-lexer/full.hthr` in the project
folder: `step(st, b) = step_full(st, class(b))`, about two dozen arms over
three functions) still fails with `the kernel rejected
step_native_evaluable: OutOfFuel`. Measured on the cloud box at
`claude/project-thread-dyc7dc`: `evaluable` of `class`'s code (nine
nested `match`es, 52 writes and 103 mentions, ids below 44) is about half
the fuel by itself, against roughly a tenth of that for lowering the code
and a linear pass over it; with the pairwise `disjoint` replaced by a
max-id test the check costs about as much again, so the cost is the
per-level recomputation of the id lists, not the comparisons.

## Done when

`program_evaluable`'s cost is linear in the program (up to a log), so a
tool-sized step function certifies through `compile-x86`. A likely shape: one
bottom-up pass that returns, per region, whether it is evaluable together
with its writes' minimum and mentions' maximum (the lowering allocates ids
increasingly, so `min(continuation writes) > max(prefix mentions)` decides
the disjointness in the common case, with the pairwise check as the
fallback), and a theorem that the pass implies `evaluable`, which the
certificate cites in place of `trivial`. The proofs that read `evaluable`'s
conjuncts stay as they are.

## Resolution (2026-11-07)

Not the min/max-with-fallback shape: the lowering allocates a match's join
id before the comparison its condition reads, so an arm's writes are
routinely below its prefix's mentions and the fallback would have run at
every level. Instead `StructuredRegion::scan` (`function_ir_eval`) walks a
region once in evaluation order with the ids mentioned so far as marks (a
`List<Bool>` bitmap): a write must find its id unmarked, every mention marks
its id, a conditional's arms start from the same marks with the condition
marked and are joined after, and a loop's or function's body starts from its
parameters. That is `evaluable`'s condition read the other way round, so it
accepts exactly what `evaluable` accepts (probes in
`lib/_tests/native/function_ir/function_ir_eval_tests.hthr`, each refusal
beside `evaluable`'s). `scan_sound`/`scan_marks`/`scan_keeps` prove it, and
`program_scan_evaluable` gives `program_evaluable`, which the certificate
cites; `eval_computes` and the proofs reading `evaluable`'s conjuncts are
unchanged.

The certificate (`crates/cli/src/native/verified.rs`, `evaluable_text`) also
checks one function per declaration (`{prefix}_scanned_{k}`, joined by
`program_scan_drop`), since the fuel is per declaration. `compile-x86` of the
self-hosted lexer's `step` now certifies; its largest declaration is
`step_full`'s scan, about 29% of the fuel. What remains is the scan's cost
per id (marks are indexed by unary ids, so a function costs the sum of the
ids it mentions): [[function-ir-scan-id-cost]].
