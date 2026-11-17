---
title: omega's guard round: open a recursion past its first element and a case arm's match
status: open
thread: Make compiler correctness proofs elegant
labels: [tactics,omega,proofs]
area: tactics
milestone: [tac-general]
created: 2026-11-16
updated: 2026-11-16
---

`omega`'s guard round (`split_bool_guards`, `crates/elab/src/omega_cert.rs`) reads a guard written with `&&` and opens a Bool definition by one δ step, but stops at two shapes `known` now reads (issues/bool-guard-facts-by-known.md):

- **A recursion over a list literal past its first element.** From `h: all_fit([a, b, c]).IsTrue()`, `omega` proves `a <= 8` and not `c <= 8`: the reduct's tail is the induction hypothesis's call, a β-redex `(λ i => all_fit(…))(k)` at its head, which `guard_shape` reads as `Other` and so never opens (CutSat's model `c = 9`).
- **A case arm's instance of its motive.** In `Layout::call_fits_parts` (`lib/native/native_compile_correct.hthr`) the arm's `f: Bool::IsTrue(match Some(proc) { None => False, Some(proc) => … && (args.len().leb(6) && …) })` is not read: a `match` on a constructor is `Other` too, so `omega(f)` cannot prove `args.len() <= 6` and the proof writes `Nat::leb_sound(args.len(), 6, known)`.

`known_guards.rs` handles both by contracting a head β-redex (`spelling::beta_head`) before reading a guard's shape, and by opening an `Other` guard through the oracle's reduct walk to its first reduct with a connective. The same two steps in `guard_shape`'s callers would let `omega(fit)` read `words_fit([fd, at, len, result])` as four facts.

## Done when

`omega(h)` proves `c <= 8` from `h: all_fit([a, b, c]).IsTrue()`, and `omega(f)` proves `args.len() <= 6` in `Layout::call_fits_parts`.
