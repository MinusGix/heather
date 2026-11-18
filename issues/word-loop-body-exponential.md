---
title: A `for` over words is exponential in the statements of its body
status: closed
labels: [performance,elab,loops]
area: language
created: 2026-11-18
updated: 2026-11-18
code: crates/elab/src/measure.rs subst_shared
---

Found by [[elaboration-cost-overview-2026-11-18]]. A `for i in 0..8 { r.a := r.a + i; … }` over a `u64` field, in a plain `fn` (no `runtime` prefix), with `logic`, `bitvec` and `bitvec_omega` imported. Measured 2026-11-18 on the cloud box, test-profile binary, whole declaration:

| statements in the body | 4 | 6 | 7 | 8 | 16 |
|---|---|---|---|---|---|
| time | 0.7 s | 2.8 s | ~10 s | 38 s | killed at the 600 s rail |

At eight statements, 18 s were the declaration body and 7 s were unattributed, with 66 M local-substitution nodes (1.9 M at four). The same loop over a `Nat` field, and the same eight statements with no loop, both stay flat at about 0.45 s. So does a body that never reads `i` (`r.a := r.a + 1`).

## Where it goes

- `elab_loop_decl` (`declarations.rs`) reads a loop over a range of numerals at `Nat` first, and at `u64` only once that reading is refused (`loops::Ranges::Words`). Here `r.a + i` mixes `u64` with a `Nat` `i`, so the whole family is elaborated twice, and the first reading fails only after its own search.
- 73% of samples are in `op_carrier_head` (`dispatch/operator.rs`): to find an operator's carrier, it probes `elab_infer` on the leftmost operand inside a rolled-back `probe`. Counting those probes and how deeply they nest: **2,166 probes at four statements, nested up to 3 deep; 25,290 at six, up to 5 deep.** The operand's spelling holds the statements before it (the lifted body threads `r` through each assignment), so each probe re-elaborates expressions whose operators probe again.

## Benchmarks

`scripts/bench-frontend --filter loops/word-body`: four to seven statements over `bitvec_omega`'s closure, slope 3.47 on 2026-11-18, each statement past five doubling the time. Its band is recorded, not claimed; a fix leaves it from below.

## Done when

The family's slope is near 1. The two levers are independent: the carrier probe should not re-elaborate an operand the real elaboration will elaborate again (keep its result, or read the carrier from a cheaper source), and the range's reading should be chosen before the body is elaborated, not by a failed elaboration.

Not yet checked: how much of the library's `runtime fn` time this is. The library's word loops have few statements per body, and `Sha256::rounds`'s cost is mostly the generator ([[runtime-generator-link-cost]]).

## Log

- 2026-11-18: Fixed. The cause was neither lever above. Timing each generated declaration of the loop's family with its body's size showed `R::f_loop#ext`, `R::f_loop_unfold` and `R::f_loop#induct#body` growing, their bodies' added size doubling per statement. Those companions substitute each `let` into the next (`measure::Respell::let_apply`, `inline_lets`, and `branch_equations::inline_ty` for the principle), and `r.a := r.a + i` is `let r = r with { a = r.a + i }`, which reads `r` twice, so `k` statements spelled the first value 2^k times. The carrier probes only multiplied that. The `Nat` reading is refused in under a millisecond, so reading it first costs nothing worth removing. Over `Nat` the loop is a fold with no measured companions, which is why it stayed flat.

  `measure::subst_shared` binds a value that is read more than once (and is not a variable or a literal) once, by a block `let __dec_shared_<name> = v;`, equal by ζ. The three substitutions use it.

  Measured on the cloud box, 2026-11-18: `scripts/perf ab` on the eight-statement loop, cold, three samples: wall 39.9 → 9.2 s, every sample separate (the rest is the imports), `unify_calls` 385 k → 15 k, `syntax_eq_nodes` 24.1 M → 7.0 M. Sixteen statements, which hit the 600 s rail, check in 1.9 s warm. `loops/word-body` now sweeps 8..64 statements: slope 0.75 under a fixed second of setup. Whole library cold with the change, `--expectations`: ok, 704 expected refusals matched.

  The loop's induction principle is still refused, before and after: [[word-loop-induct-principle-decide-names]].
