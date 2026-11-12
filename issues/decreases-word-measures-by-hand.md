---
title: A loop counting in a machine word proves its decrease by hand: the discharge never tries bv_omega
status: closed
labels: [elaboration,termination,bitvec,ergonomics]
area: language
created: 2026-11-12
updated: 2026-11-12
---

A loop that counts in a machine word proves its decrease by hand at every site. All nine loops of `lib/native/crypto/sha256_block.hthr` and `sha256_stream.hthr` end the same way (2026-11-12):

```heather
runtime fn sha256_zero(ctx: List<u8>, cn, i: u64) → Mutated<List<u8>, u64>
    decreases (64 - i).toNat() {
    match h: i.unsigned_lt_bit(64) {
        False => Mutated(ctx, i),
        True => { … sha256_zero(ctx, cn, i + 1) },
    }
    on ?dec1 := {
        let below = bitvec_omega::unsigned_true(64, i, 64, h);
        bv_omega
    };
}
```

Three separate things make the tail necessary. Probes, each a `runtime fn` of this shape:

1. **The automatic discharge runs `omega` and nothing else.** Without the `on ?dec1`, the refusal is "`64 - i + 1.toNat < 64 - i.toNat` was not proved automatically (`omega` got stuck …)": `omega` holds `toNat(64 - i)` and `toNat(64 - (i + 1))` as two unrelated atoms. `bv_omega` is the tactic that reads them, and the discharge never tries it. The same holds for a `while i.unsigned_lt_bit(64) decreases (64 - i).toNat()`, which has no place to write the proof at all, so a `while` over a word cannot be written today.
2. **`bv_omega` does not read the test as the test is written.** With `h: i.unsigned_lt_bit(64) = True` in scope it needs `bitvec_omega::unsigned_true(64, i, 64, h)` bound by hand first.
3. **`bv_omega` does not finish from the proposition either.** With the test written `if h: i < 64` (which elaborates, and which a plain `runtime fn` compiles), `h: i < ofNat(64)` is in scope and `bv_omega` answers "`64 - (i + 1)` may borrow; `omega` could not prove `toNat(i) + 1 <= 64`", with a model in which `toNat(ofNat(64)) = 65`: the literal's `toNat` inside the hypothesis is an atom, not sixty-four.

## Wanted

- The measure discharge tries `bv_omega` when the obligation or a guard in scope mentions `BitVec` (or, more generally, a short list of closers by the measure's carrier), after `omega`.
- `bv_omega` reads `a.unsigned_lt_bit(b) = True`/`= False`, `a.unsigned_le_bit(b) = …`, `a.eq_bit(b) = …` and the propositions `a < b`, `a ≤ b` from the context itself, and evaluates the `toNat` of a literal wherever it meets one.
- Then the loops above lose their `on ?dec1` blocks, the test can be `if i < 64`, and `while i < 64 decreases (64 - i).toNat()` discharges. Whether the generator takes the function a `while` lowers to inside a `runtime fn` is the next question and is not known: the probe stops at the measure.

Done when: the nine loops of the two SHA-256 modules and the loops of `lib/lang/lexer` carry no `on ?dec1`, and a probe in `lib/_tests` holds each of the three readings. Related: [[bv-omega-binder-captures-t]], [[measure-inference]], [[decreases-self-parameter]].

## Log

- 2026-11-12: Done for plain fns: an obligation nobody discharges falls back from omega to bv_omega when it is over a word's toNat (measure::CLOSER, Checking's arm), and bv_omega reads unsigned_lt_bit/unsigned_le_bit/eq_bit = True/False and a < b, a <= b at a word from the context (bitvec_omega::unsigned_le_true/false, unsigned_lt_prop/le_prop), a literal operand's toNat evaluated through the existing comparison bridge. Probes in lib/_tests/std/tactic/bitvec_omega_tests.hthr: match h:, if h: i < 64 and while i < 64 decreases (64 - i).toNat(), with a negative control. The SHA-256 and lexer loops keep their on ?dec1 for now: those modules are another round's (PR #551); dropping the blocks is a follow-up edit there.
