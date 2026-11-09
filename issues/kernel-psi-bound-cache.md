---
title: Bind GlobalCache to its Ψ in the type
status: closed
labels: [kernel,soundness,refactor,state-machine]
area: kernel
created: 2026-11-02
updated: 2026-11-09
---

Bind a `GlobalCache` to the Ψ it was built for in the type, so a mismatched pair cannot be constructed.

## Problem

`reduce::GlobalCache` memoizes rescoped bodies and signatures by `GlobalVar` and is sound for one Ψ only: "an entry surviving a push would answer about the wrong binding: a soundness bug, not a slowdown" (`crates/kernel/src/reduce.rs` ~135). The invariant that `cache` belongs to `psi` is kept by hand: `push_tele` rebuilds it in both `typing::Env` and `conv::Env`; twelve `typing::Env { psi: psi.clone(), cache: Rc::new(GlobalCache::new()), … }` literals pair them; the `pub(crate)` `conv_*_cached` entries take the two as separate arguments; and `pub fn Defs::transparent_cached(psi, cache)` plus `pub struct GlobalCache` are used from the elaborator as `Reader { psi, cache }` pairs (`crates/elab/src/host.rs` ~92, `function_ir_source/program.rs` ~1079). Survey: `docs/implicit-state-machines-survey.md` §3.

No mismatch exists today, but it is a TCB soundness invariant the type system does not see, reachable from a public constructor.

## Proposal

A `ScopedGlobals { psi, cache }` (name open), built only from a Ψ, whose only Ψ-changing operation is the telescope push that rebuilds the cache. `Defs::transparent_cached` and the `*_cached` entries take it; the twelve `Env` literals become one constructor; the elaborator's readers hold one. `GlobalCache::new` stops being public.

Kernel change: run `scripts/bench --check` (the cache exists for performance, `docs/conversion-query-arena-pooling-design.md` §3), and keep the zero-dependency rule.

## Related

Filed together from the implicit-state-machines survey (`docs/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[elab-field-lifetimes-explicit]], [[module-pass-state-machine]], [[decl-attempt-lifecycle]], [[goal-slot-state-enum]], [[kernel-checker-mode-enum]].

## Log

- 2026-11-05: gardener: cites a file it shares with [[conversion-typed-eliminator-congruence]] (`crates/kernel/src/reduce.rs`); [[elab-emits-normal-form-of-matched-type-argument]] (`docs/conversion-query-arena-pooling-design.md`); [[reducer-step-frame-size]] (`crates/kernel/src/reduce.rs`).
- 2026-11-08: 2026-11-08: still open and accurate in the kernel second pass (`docs/kernel-implicit-state-review.md` §4): 17 `GlobalCache::new()` pairings in `typing.rs`, 2 in `conv.rs`. Addition: `Defs::transparent` is also "only sound at a computing layer" (`reduce.rs` ~192), enforced only at `Conv::defs`. The `ScopedGlobals` could be the only way to obtain a transparent `Defs`, as `scope.defs(layer)`, returning opaque at layer c. Same pairing shape one level down: [[value-memo-evaluation-mode]] (the value arena and its `Defs`).
- 2026-11-09: done by identity: `GlobalCache::for_psi` records Ψ's bindings identity, and `Defs::transparent_cached` consults the cache only beside that Ψ (debug builds assert; release drops the memo). `GlobalCache::new` is gone, so every pairing, the elaborator's readers included, names its Ψ. A `ScopedGlobals` pair type was not needed for the guarantee. Unit tests in `reduce.rs` (`global_cache_tests`). The layer condition on `Defs::transparent` stays documented (`docs/kernel-implicit-state-review.md` §4).
