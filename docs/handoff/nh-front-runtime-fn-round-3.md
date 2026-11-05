# Handoff: nh-front runtime fn round 3 (from Atelier, interrupted 2026-11-05 14:27 UTC)

Worktree at handoff: local Atelier worktree (now pushed; use the branch)
Branch: atelier/nh-front-runtime-fn-round-3-fold-1o0a0e (pushed 2026-11-05; 5 behind origin/master at handoff). Probes
in probes/rt3/ (p_big.hthr, p_fuel.hthr).
Issue: issues/runtime-fn-default-setup.md (milestone nh-front). Design: docs/runtime-fn-setups-design.md (new §16.10).
Old session (avoid resuming, ~3 MB transcript): 902dd89f-8669-4c5b-bbe6-06f982db1aa3

## Goal
Move loop and Bool-helper programs onto `runtime fn` so `compile-x86` no longer needs the Rust reflector, then delete
crates/elab/src/function_ir_source/. Allowed to split into two rounds: land the loop lowering first.

## Done (committed, implementation complete for this round)
- `rt`: `Ty::Count` (a Nat held in a 64-bit word), `Op::ToNat` (no code), `Tm::Case` (match on a Count).
- New module lib/native/runtime/rt_loop.hthr: tail-mode lowering with `Tm::tail_sound`; fuel loops `Fun::fuel_sound`
  (needs only the two structural-recursion equations, both `refl` thanks to #428); measured loops `Fun::measured_sound`
  (2^64-1 passes, rests on `Fun::Guarded`, built from `f::ext`/`f::irrel`).
- `f::ext` and `f::irrel` now have spellings like `f::rec`/`f::body` (small change in crates/elab/src/lib.rs, the only Rust change).
- Probes in lib/_tests/native/runtime/rt_loop_tests.hthr: `sum_down` (fuel) and `count_down` (measured) check; a step
  reading `+` as `-` is refused. lib/native/runtime, lib/_tests/native/runtime and lib/lang/facts check.
- Docs: design §16.10 and the issue log updated (c6429d20). `Fold` over byte buffers is off the path (no x86 example folds a buffer).

## Not done for this round
`scripts/test --pr` was running (native certificate gates included) when Minus interrupted; its result is unknown. No PR yet.
Next: rebase on origin/master, rerun `scripts/test --pr`, push, open the PR.

## Next round (from the thread's own list, in order)
1. Setup/Compile plumbing: `Fun::lower` dispatches to the loop lowerings, with the function's equations as a hypothesis the generator proves.
2. `Count` parameters in calls, so a caller can pass `w.toNat()` as fuel.
3. Reflector: read a fuel recursion's top `match` on Nat (needs a host change in `Arms`), and a measured function's body from `f_unfold` plus its measure.
4. `compile-x86` on the loop examples, then delete crates/elab/src/function_ir_source/.
5. `Bool` helpers, separately.
