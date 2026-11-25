---
title: A function's promise has a precondition and no postcondition
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`lib/lang/ownership/call_check.hthr`'s `FnSafe(sig, pre, mean, run)` lets a callee assume `pre` of its words, and promises only that its run agrees with its meaning ([[ownership-checker-call-and-write-view]], log of 2026-11-25). It says nothing about *what* the meaning answers. So a caller whose residual depends on a callee's answer cannot discharge it: `Checks.discharge` is quantified over every world, and nothing ties the world's answer to a fact.

The case that will meet it first: a callee answers an index or a window it found, and the caller writes there beside a view it holds. The residual `Apart(…, Var(z), …)` reads the word `z` the call bound; proving it needs the callee's promise that `z` is, say, past the view.

## Shape of the fix

A postcondition beside the precondition, as a proof parameter of the kernel type (§15.8: "residual preconditions are not extra data"): `post(ws, answer)`, which the callee proves of its meaning and the caller assumes at the call. The world's meaning stays abstract; `FnSafe` gains `post(ws, mo)`. The checker's data does not change: a residual reads the word the call bound, and its proof is the caller's, from the callee's `post`.

## Done when

A caller with a residual over a callee's answer is accepted, its residual discharged from the callee's postcondition and nothing else of it, with a `¬` control where the postcondition is dropped.
