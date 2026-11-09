---
title: Derive the typing memo's keys from one scope sub-struct
status: open
labels: [kernel,state-machine,soundness,refactor]
area: kernel
created: 2026-11-08
updated: 2026-11-08
---

Build the typing memo's three keys from one sub-struct of the checker's `Env`, so a scope field a rule reads cannot be left out of a key.

## Problem

`crates/kernel/src/typing.rs` `Scope` (~1343), `TyScope` (~1379) and `SigScope` (~1406) each copy `psi` (as `bindings.identity_addr()`), `gamma_base`, `univs`, `layer` and `under_box` out of `Env` (~973) in their own `of`. A memo hit is sound only when the key holds every part of the scope a rule reads. The next side condition added to `Env`, as `under_box` was for `checked_spelling_admitted`, has to be added to three structs and three constructors by hand, or the memo answers across it.

Ψ is keyed by `bindings` alone. `GlobalCtx::sealed` and `withheld` (`term.rs` ~1836) change what δ does, and the keys are sound only because a `Tc` lives for one gate over one Ψ. That invariant is not stated. The verdict cache in `crates/cache` mixes `withheld` into its key explicitly.

Review: `docs/kernel-implicit-state-review.md` §3.

## Proposal

Split `Env` into a `Copy` `JudgmentScope { psi_id, gamma_id, gamma_base, univs, layer, under_box }` and the rest (`cache`, metrics). Derive the three keys from `JudgmentScope`, and `debug_assert!` at the checker's entry points that every `Env` it builds shares the gate's `sealed`/`withheld`. No behaviour change: identical `--timings` counts.

## Related

[[kernel-checker-mode-enum]], [[kernel-psi-bound-cache]], [[kernel-typing-memo-on-node-identity]].
