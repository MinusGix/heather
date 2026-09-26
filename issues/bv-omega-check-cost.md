---
title: bv_omega costs several times the hand proofs it replaces
status: open
labels: [performance,proofs,bitvec,omega]
created: 2026-09-26
updated: 2026-09-26
---

`bv_omega` checks the word facts of `lib/decimal_line.hthr`, but it costs
several times the hand proofs it replaces. It is correct, and too slow for
the library to switch to. The measurements are in
[[bitvec-nat-lifting-tactic]]'s log of 2026-09-26, and the emission shape is
in docs/bv-omega-design.md §2.

Three costs, in the order the probes point at:

1. **Every `omega` runs in the enclosing declaration's context.** A hand proof
   gives each arithmetic goal a lemma of its own, with only its hypotheses.
   `bv_omega`'s side conditions see everything in scope. Relevance layers
   choose which facts to refute with, but the atom table, and with it every
   certificate row, is sized by every atom reflected. That is an omega-side
   change: compact the atom table to the layer that succeeded. `place_step`
   is the case to measure (kernel gate about half its time).
2. **One normalisation `omega` per `add`/`sub` node.** It proves the node's
   value normal form from its operands'. It is a pure Nat identity over leaf
   atoms, which a certified normaliser could discharge without a search.
   Merging it into the node's bound would at least halve the number of calls.
3. **`bitvec_omega`'s own arithmetic lemmas.** `add_arith` and `sub_arith` are
   proved by `omega` over nine variables and dominate the module's check.
   Hand proofs from the Nat kit would remove that from every prefix that
   loads it.

## Acceptance

- `scripts/perf ab` on the `decimal_line` re-proofs (the probe set in the
  parent's log) shows the whole-workload total moving, not only named rows.
- `decimal_line` adopts the tactic for the facts where it is then within the hand proofs' cost (the table in the parent's log is the baseline).

## The probe set

Each file imports `bitvec`, `logic`, `nat`, `omega`, `bitvec_nat`, `bitvec_omega` and
`decimal_line`, with `bitvec_omega` and the x86 modules copied beside it under their harness
names ([[bitvec-nat-lifting-tactic]]'s log has the numbers).

```text
theorem bv_times256_value(y: BitVec(64), v: Nat, value: y.toNat() = v * 1, bound: v * 256 < 1152921504606846976):
    times256(y).toNat() = v * 256 { bv_omega }


theorem bv_raise_value(n: Nat, small: n < 16384): raise(bitvec_nat::word_of_nat(64, n)).toNat() = n * 1099511627776 { bv_omega }


theorem bv_line_state_start(n: Nat, small: n < 10000): line_state_start(n).toNat() = 1099511627776 * n + 43758137392 { bv_omega }


theorem bv_line_start_value(n: Nat, small: n < 10000):
    line_start(BitVec::ofNat(0x401000), bitvec_nat::word_of_nat(64, n)).toNat() = 0x401000 + line_skip(n) {
    let skip = line_skip_le(n);
    let zeros = leading_zeros_value(n, small);
    bv_omega
}


theorem bv_line_length_value(n: Nat, small: n < 10000):
    line_length(bitvec_nat::word_of_nat(64, n)).toNat() = 5 -line_skip(n) {
    let skip = line_skip_le(n);
    let zeros = leading_zeros_value(n, small);
    let r: (line_length(bitvec_nat::word_of_nat(64, n)).toNat() + line_skip(n) = 5) = bv_omega;
    let back = Nat::sub_add_cancel(line_skip(n), 5, Nat::le_trans(line_skip(n), 3, 5, skip, trivial));
    omega
}

theorem bv_place_step(s: BitVec(64), r, h, c, w, q, rest: Nat,
    value: s.toNat() = 1099511627776 * r + h, low: h + w < 1099511627776,
    parts: r = c * q + rest, remainder: rest < c, one: q <= 1,
    fits: 1099511627776 * r + h < 1152921504606846976, c_fits: 1099511627776 * c < 1152921504606846976):
    place(s, BitVec::ofNat(1099511627776 * c), BitVec::ofNat(w)).toNat() = 1099511627776 * rest + (h + w * q) {
    let big = BitVec::ofNat(1099511627776 * c, n := 64);
    let weight = BitVec::ofNat(w, n := 64);
    let test: (s.unsigned_lt_bit(big) = Succ(s.toNat()).leb(big.toNat())) = bitvec_nat::unsigned_lt_nat(64, s, big);
    (match q as λ k => (r = c * k + rest) → (k <= 1) →
        place(s, big, weight).toNat() = 1099511627776 * rest + (h + w * k) {
        Zero => λ parts one => {
            let under: (Succ(s.toNat()) <= big.toNat()) = bv_omega;
            let kept: (s.unsigned_lt_bit(big) = True) = trans(test, leb_yes(Succ(s.toNat()), big.toNat(), under));
            let same: (place(s, big, weight) = s) =
                j(sym(kept), λ b _ => (match b { True => s, False => s.sub(big).add(weight) }) = s, refl);
            let moved: (place(s, big, weight).toNat() = s.toNat()) = @cong(λ (v: BitVec(64)) => v.toNat(), place(s, big, weight), s, same);
            bv_omega
        },
        Succ(k) => (match k as λ k2 => (r = c * Succ(k2) + rest) → (Succ(k2) <= 1) →
            place(s, big, weight).toNat() = 1099511627776 * rest + (h + w * Succ(k2)) {
            Zero => λ parts one => {
                let over: (big.toNat() < Succ(s.toNat())) = bv_omega;
                let taken: (s.unsigned_lt_bit(big) = False) = trans(test, leb_no(Succ(s.toNat()), big.toNat(), over));
                let stepped: (place(s, big, weight) = s.sub(big).add(weight)) =
                    j(sym(taken), λ b _ => (match b { True => s, False => s.sub(big).add(weight) }) = s.sub(big).add(weight), refl);
                let moved: (place(s, big, weight).toNat() = s.sub(big).add(weight).toNat()) =
                    @cong(λ (v: BitVec(64)) => v.toNat(), place(s, big, weight), s.sub(big).add(weight), stepped);
                let sum: (s.sub(big).add(weight).toNat() = 1099511627776 * rest + (h + w * 1)) = bv_omega;
                trans(moved, sum)
            },
            Succ(_) => λ parts one => false_elim(one),
        }),
    })(parts, one)
}

```
