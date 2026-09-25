---
title: Structural recursion compiles the match, not the function, so a fn can compute a wrong answer
status: closed
labels: [elaboration,correctness,recursion]
created: 2026-09-25
updated: 2026-09-25
---

A structurally recursive `fn` that names its scrutinized parameter inside the
`Succ` arm computes a **wrong answer**. The program is well typed, and the
kernel accepts the wrong equation by `refl`:

```text
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
fn sum(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => add(sum(k), n) } }
theorem wrong(): sum(2) = 4 { refl }   // accepted; the source means 3
```

Writing `Succ(k)` instead of `n` in the arm gives 3. The likely reading is
that the arm is the `elim_Nat` step, and `n` inside it is still the outer
λ's parameter. The step runs once per level, and at every level `n` is the
top-level argument, not that level's `Succ(k)`. Nothing refines the
scrutinee variable to the constructor inside its own arm for the *value*
(only the motive is refined). Found 2026-09-25 while testing `have`
([[proof-let-substitution-cost]]'s follow-up, docs/have-design.md); it is
independent of `let` and `have`.

## Acceptance

- `sum(2) = 3` by `refl`, and `sum(2) = 4` is refused. Test at a literal
  argument (it must compute) and at a neutral one.
- The fix either substitutes the arm's constructor for the scrutinee in the
  arm body, or refuses the mention by name. It does not silently keep the
  outer value.
- Sweep: whether `lib/` or the showcase has a recursive arm that mentions its
  own scrutinee (a wrong computation that no `refl` pinned).

## What it assumes from elsewhere

- **[[ih-generalization]]** owns motive generalization. Assumed here: only
  that it never rebinds the scrutinee in the arm *body*.

## Log

- 2026-09-25: DIAGNOSED (investigation, no code changed; debug CLI probes, each wrong value pinned by `refl`). **The structural lowering treats the recursion-driving `match` as the recursion, where the source means the function.** The `match` becomes the eliminator, and a self-call `f(k)` becomes that eliminator's hypothesis, i.e. "this match at k". Everything outside the match (the surrounding expression, earlier `let`s and `have`s, and the parameter itself) is evaluated **once, at the top level**. So the defect is wider than filed. It has two mechanisms, and both hold on `Nat` and on declared inductives (the `Wf` route):
  - **M1, the parameter reads its top-level value inside the step.**
    - `Succ(k) => add(sum(k), n)` gives `sum(2) = 4` (means 3).
    - Through a `let m = n` alias it gives `g(2) = 4`.
    - Through a `have m = n` it gives the same wrong value.
    - Two levels down (course of values) it gives `h(4) = 8` (means 6).
    - On a list, `C(h, t) => add(w(t), size(xs))` gives 4 (means 3).
    - The `Zero` arm is affected too: `Zero => n` sees the top-level `n`.
  - **M2, the match is not the whole body.**
    - `add(1, match n { …, Succ(k) => f(k) })` gives `f(2) = 1` (means 3).
    - `add(match n {…}, n)` gives `e(2) = 2` (means 3).
    - `Succ(match xs {…})` on a list gives 1 (means 3).

    The `+1` or `Succ` around the match is never re-run per level.

  **`decreases` recursion is correct on all of these.** `sum`, `f` and the `have` variant each compute the source value, because the measure route elaborates the whole body as a function of that level's parameters (`__dec_ih : (x: Nat) → Lt(x, …) → Nat`, with a fresh `n` per step). It is the reference for the intended meaning.

  **Theorems are not at risk.** The kernel checks the statement, so the lowering only picks a different proof of the same fact. What is wrong is the *meaning* of a `fn`: every certified statement about `sum` is true of the compiled term, not of the source.

  **Sweep.** A throwaway syntactic scanner over the parsed `lib/`, `docs/showcase` and test corpora looked for a match on a parameter with self-calls in its arms, naming that parameter or an alias of it inside an arm (M1), or sitting outside tail position (M2). It flagged the seven probe cases exactly and three library items:
  - **`parser_diagnostics::insert_expected` is a real wrong answer.** Its `Inl(_) => expected` names the decreasing list, so `insert_expected(2, [1, 2, 3]) = [1, 1, 2, 3]` checks by `refl`. It feeds `merge_error`, so merged parse failures list duplicate expected codes. No theorem mentions it.
  - `certgen_cert::cert_chain` is a false positive: the flagged match is on `ih`, a parameter passed unchanged.
  - `Nat::le_trans` is a theorem, so it is harmless.

  The scanner is in the session scratchpad; it is heuristic and not committed.

  **Fix options, costed against the code:**
  1. **Refuse** (small, uniform). In a `fn` body, reject a recursion-driving match that is not in tail position, or whose arms mention the decreasing parameter. Tail position means the body result, block results, and arms of matches whose scrutinee does not involve it. For the arm check, test the elaborated arm term for the parameter's variable, which catches inlined aliases, plus any `have`-local bound above the match (conservatively). Each message names the rewrite: the constructor instead of the parameter, the surrounding code moved into the arms, or `decreases`. The tail flag needs one `Cx` bit, cleared at the expression dispatcher for anything other than a block or match. That costs a clone only while the bit is set, which is only along the body's tail spine.
  2. **Make M1 legal by substitution.** In each arm of a recursion-driving match, replace the parameter's variable by the arm's constructor term (`Succ(k)`, `C(h, t)`). This is valid when no later binder's type mentions the parameter; otherwise refuse. It is cheap for `Nat`, and per-route work for `Wf`, indexed and forded families. M2 stays refused.
  3. **The principled lowering:** put the eliminator at the function's root, and elaborate the whole body once per constructor with the parameter aliased to that constructor. A `match` on a now-known constructor then selects its arm statically, and self-calls take the hypothesis. This fixes M1, M2 and the `have` case together, at the price of elaboration and term size scaled by the constructor count around the match, and a rework of every route (`Nat`, `Wf`, indexed, forded, mutual, course of values, the generalization wrapper).

  Recommendation: 1 now, so nothing can silently compute the wrong thing, together with the one-line `insert_expected` fix and a `refl` pin on it. Then 2 for `Nat`, where M1 is the common way to write it. 3 only if the tail restriction proves annoying in practice. Until then, `decreases` is the escape hatch that already has the right meaning.
- 2026-09-25: LANDED, option 1 (refusal) plus the library fix. Full suite 2987 passed, 0 failed.
  - **What is refused, in a `fn` body only** (a theorem's meaning is its statement, which the kernel checks):
    - the decreasing parameter read inside its recursive `match`, directly, through a `let` bound from it above, or through a `have` bound above;
    - a recursive `match` that is not the body's result;
    - a recursive `match` under a branch that depends on its parameter.

    Each message names the rewrite: this level's pattern, moving the code into the arms, or `decreases`. The tests are in `crates/elab/tests/recursion_meaning.rs`.
  - **Mechanism** (all in `recursion.rs` apart from the hooks):
    - `Cx::tail` is the body's result spine. It is cleared at the expression dispatcher for anything other than a block or a match, and at bound values; it records each tail scrutinee.
    - `arm_scope` gives the arms of a match that syntactically looks recursive a `RecursionScope`.
    - Name resolution **records** a top-level read there.
    - `confirm_recursion` in `elab_self_call` turns the recorded placement or read into an error only once a self-call is actually lowered. Reads after that point error at once.

    Deferring the report is what the method-call case needs. The syntax cannot tell `contents.size()` on `List` from `Box::size`'s self-call; the first version refused `type_members`' `Box::size` for that reason. An arm's own pattern fields are aliases too, so a read only counts for aliases bound before the match (`aliases_before`). `Cx::prefix` drops the positional state.
  - **Library:** `parser_diagnostics::insert_expected` now returns `Cons(head, tail)`, pinned by `insert_expected_present_deeper` (`[1, 2, 3]` stays `[1, 2, 3]`). The full suite found no other library or test source the refusal rejects. My scanner's other two hits were a false positive and a theorem.
  - **Residue:** making the refused spellings legal (substitution for `Nat`, then the function-level lowering) and the type-valued `fn` gap go to [[fn-recursion-means-the-function]].
