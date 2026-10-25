---
title: Compile a function defined by well-founded recursion on a measure to a loop
status: open
labels: [native,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-25
updated: 2026-10-25
---

[[function-ir-verified-loop-planning]] compiles recursion on an explicit
fuel, `h(fuel, x…)` called as `h(w.toNat(), …)`: the loop's passes are the
fuel, and the program agrees with the source exactly, exhausted bit and
all. A function written by well-founded recursion on a measure of its words
(`Wf`) has no fuel; its loop needs a bound computed from the measure at
entry, and its agreement needs the theorem that the loop never runs out
(`function_ir::loop_runs_unexhausted`: bound the measure plus one, or the
measure where it is positive at every pass).

Two routes:

- Reflect the `Wf` recursion's step the way a fuel's `Succ` arm is
  reflected, and state the agreement by `Wf` induction on the measure
  instead of `Nat` induction on the fuel, the exhausted branch discharged
  by `loop_runs_unexhausted`'s argument.
- Or have the source supply the bound (a fuelled helper, as today) and
  prove once in the library that a fuelled helper with enough fuel is the
  `Wf` function: the compiler then needs no new reflection.

The second is less compiler and more library; it also gives the user's own
fuelled helpers a theorem. Elaboration cost of `Wf` unfolding at open
arguments is the unknown either way.

## Log

- 2026-10-25: Probed in the loops-anywhere round, not built. A word loop by measure elaborates today: `fn count(n, acc: BitVec(64)) → BitVec(64) decreases n.toNat() { match h: n.eq_bit(BitVec::ofNat(0)) { True => acc, False => count(n.sub(BitVec::ofNat(1)), acc.add(n)) } on ?dec1 := pred_lt(n, h); }` checks, with `pred_lt` a dozen lines (`toNat_sub`, `Nat::sub_lt_of_pos`; `omega` does not see through `toNat(n) - toNat(ofNat(1))`). What it does not get is `count_unfold`: the generator refuses it ("the lifted `count#obl_1` was refused (this has type `__dec_scrut_N = False`, but `eq_bit(n, ofNat(0)) = False` is expected here)"), because a `match` on a computed scrutinee is outside its fragment (docs/decreases-unfolding-design.md §3, the `merge` amendment). Every word loop decides on a computed scrutinee, so neither route above can lean on `f_unfold`.

  The route that needs no `f_unfold`: state the loop against `f#rec` itself. `f(x̄) = f#rec(Succ(e), x̄, lt_succ_self(e))`, and `f#rec(Succ(k), x̄, h)` unfolds definitionally to `f#body(k, λ ȳ h' => f#rec(k, ȳ, h'), x̄, h)`, whose self-calls are `f#rec(k, ȳ, p)` with `p` built from the lifted `f#obl_N`. So the pass agreement is the fuel loop's, with the source run carrying a proof: the invariant is `e(state) < Succ(r)` for the loop's remaining count `r`, the count starts at the measure word (`e = w.toNat()`), and each pass keeps it because the obligation gives `e(next) < e(state) <= r`. What is new against the fuel loop: (1) `loop_eval_agrees_from` over a run indexed by that invariant (a library theorem, by `Nat` induction on the count as today); (2) the exhausted branch is unreachable rather than the `Zero` arm: at `r = 0` the state's measure is `0`, so the region the IR runs there is the pass with every recursion leaf replaced by anything, and its agreement discharges each leaf from the leaf's own obligation (`e(ȳ) < 0`), which the certificate has to name per leaf; (3) the reflector reads `f#body` rather than a `Succ` arm. (2) is the part with no precedent in the certificate generator.

  Kept open for that round; nothing on master refuses differently than before (a `decreases` function called from a compiled function is refused at its recursor: "`count#rec` is not an operation this compiler lowers, nor a function of BitVec(64) words it can call").
