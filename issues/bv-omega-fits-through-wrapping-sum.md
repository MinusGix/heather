---
title: bv_omega and a window that fits: a word sum that may wrap, the spellings that are true, and the check that gives the proof
status: closed
labels: [tactics,bitvec,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Met writing a push through the arena's `store` ([[arena-handles-push-and-new-vec]], log of 2026-11-25): a test in the code of the shape `base + len < 16` on words does not give `bv_omega` the fact the window's `fits` wants, `base.toNat() + len.toNat() <= 16`, so the proof had to come from the handle's invariant instead of from the test the code runs.

As stated the implication is false, and `bv_omega` is right to stop: a sum of words may wrap, and `(base + len).toNat() < 16` holds at `base = 2^64 - 1`, `len = 2`. So this is two questions, not one defect.

## Scope

- **Reproduce and classify.** The exact goal and hypotheses at the arena's push; which spellings of "the window fits" are true as natural-number facts (`len <= limit ∧ base <= limit - len`; a sum with a carry test; a sum of two words each known below `2^63`) and which of those `bv_omega` proves today. A table of probes in `lib/_tests`, each a theorem or a `¬` theorem.
- **Fix what is a gap.** Where a true spelling is refused, make `bv_omega` read it (the tactic takes a word apart through `add`, `sub`, `ofNat` and byte splits; `docs/proof-patterns.md` has what it cannot read yet), or record why not.
- **Say it when the model wraps.** Where `bv_omega` stops with a counter-model in which a word sum wrapped, the report should say that the sum may wrap and name a spelling that does not, since the reader's first guess is that the tactic is weak.
- **The check that gives the proof** (vision principle 13: a runtime check is a helper that discharges an obligation). A library function on words, compiled as a `runtime fn`, that tests whether `base` and `len` fit under a limit without wrapping and whose `True` answer yields the natural-number fact, found by a found proof (`:= bv_omega` or an evidence rule) under `if h: …`. The arena's push is the customer: its proof then comes from the test the code runs.

## Done when

The probe table is in the library, each true spelling is proved by `bv_omega` or has a recorded reason, a wrapping counter-model is reported as one, and a function of `Arena` that pushes after the fitting check compiles with its `store` proof found from that check.

## What it assumes from elsewhere

- **[[runtime-record-calls-erased]]** (closed) gives a record function calling `Arena::store` with a found proof.
- **[[bv-omega-word-arithmetic-modulo]]** owns masks and borrowing subtraction modulo a power of two; not this.

## Log

- 2026-11-25: Round (branch `claude/bv-omega-fits`). Done:

    - **Probe table**, `lib/_tests/native/runtime/word_fits_tests.hthr`, goal `base.toNat() + len.toNat() <= 16` (or `<= limit.toNat()`):

      | spelling | true? | `bv_omega` before | now |
      |---|---|---|---|
      | `len <= L ∧ base <= L - len` (and base first) | yes | proved | proved |
      | `base <= 16 ∧ len <= 16 ∧ base + len <= 16` (alloc's) | yes | proved | proved |
      | `base, len < 2^63 ∧ base + len <= 16` | yes | proved | proved |
      | carry test `base <= base + len` (or `len <= …`, or the `<=` bit) beside the sum | yes | refused | proved |
      | `window_fits(base, len, L) = True` | yes | refused | proved (and `= False` gives `L < base + len`) |
      | `base + len < 16`, `base + len <= L` | no (`¬` theorem at `2^64 - 1`, `2`) | refused, goal step | refused, says the sum wraps |
      | `base <= 16 ∧ base + len <= 16` | no (`¬` at `1`, `2^64 - 1`) | refused | refused, says the sum wraps |

    - **Tactic** (bv-omega-design §5.2): a sum or difference at a literal width whose side condition failed where a fact mentions it was a fact left out, which also lost a carry test. It is now recorded (`Generated::wrapping`) and the next round keeps it whole and reads it through `toNat_add_mod`/`toNat_sub_mod`, so the facts about it are taken and the carry is a case of the remainder's quotient. Only those words: a word §5.1 keeps whole for another reason stays a plain leaf. A refusal over a sum that may overflow (diagnosed, or a goal step after such a fact was left out) now says a sum of words wraps, that a test of `a + b` does not bound `a` and `b`, and names `b <= limit ∧ a <= limit - b`, `window_fits`, or a carry test (`bv_omega::sum_wraps`).
    - **The check**: `word_fits::window_fits(base, len, limit)`, a `runtime fn` testing `len <= limit ∧ base <= limit - len`, with `window_fits_sound` (`True` → `base + len <= limit` as numbers) and `window_fits_false`; `bv_omega` knows it by name (`window_check`, only where its law is in scope), so `if ok: window_fits(…)` gives a store's found `fits`. Choice taken: a Bool `runtime fn` read by name in the tactic, rather than an evidence rule: `store`'s `fits` is a plain Nat fact found by `bv_omega`, not a relation `infer` searches.
    - **Customer**: `Arena::store_item(h, base, cap, len, x)` pushes through `Arena::store` after `window_fits(base, cap, 16)`, both proofs found; `Arena::push_fit` reads the header and calls it. Ledger rows `port_arena_push_fit_runs` (the same bytes as `push` where it fits), `port_arena_push_fit_wrapped` (a header at base `2^64 - 1`, cap 2, whose word sum is 1, is refused, the arena unchanged), `port_arena_push_fit_held`. `push_in`/`push` untouched.
    - Also: `bv_omega` reads a negated order of words ([[bv-omega-negated-word-order]], filed and closed the same round). `docs/proof-patterns.md` §3 has the rule.

    Left: the header words are parameters of `store_item` because a found proof does not read a test over a word bound by `let` to a heap read: [[found-proof-over-let-bound-read]].
