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

## Log

- 2026-09-26: Perf round opened (with the user): the bar is every re-proof within 1.5× its
  hand proof and the whole fixture at or below the hand total, at which point
  `decimal_line` adopts the tactic. Fixture: `perf/fixtures/bv_omega/`
  (`stage.sh` copies the fixture beside the two harness-named modules). Before,
  width 1: hand ~4.9 s, `bv_omega` ~35.3 s.

  Attribution (temporary per-call dump, not landed):
  - Chains are paying for the number of calls. `bv_raise_value` makes 82 `omega`
    calls (the hand proof about 14), each about as costly as a hand one. The
    certificates in the gate and in elaboration are ~62% of its 9.3 s. Fact
    elaboration is ~29%, from spelled words that grow with depth.
  - `place_step` is paying for its context. An `omega` inline in its body costs
    ~2× the same `omega` as a lemma (753 against 372 ms), and a `bv_omega` call
    costs the same multiple (1.27 s in context, 0.67 s alone, 0.56 s for plain
    Nat `omega`). Reflection alone is 1.5 s there.
  - Gap found: a word that appears only in a fact in scope gets side conditions,
    and one that genuinely borrows in the current branch sinks the call. Its
    side conditions must be optional.

  Order: normalisation by computation and root-only bounds (the call count),
  then omega's reflection sized to the connected facts (the context), then fact
  elaboration.
- 2026-09-26: Step 1 (call count) landed in the tree, uncommitted. Facts are now `t + Q = P`
  over Nat *forms* `c₁ * a₁ + (… + k)`. Forms merge by one `form_*` lemma per
  atom, with literal coefficients the checker adds, so there are no
  normalisation obligations. Bounds pass down by Nat lemmas; only roots and each
  `sub`'s borrow go to `omega`. Two rejected intermediates, measured: Omega rows
  (`dot` over Int lists) cost 12–21k kernel steps per lemma application, against
  20 for Nat; Nat-list rows 2.5–3k. List literals in types are what the checker
  pays for. Found and fixed on the way: omega read an Int `OfNat(e)` as an atom
  unrelated to the Nat `e` (now read through the Nat side); omega's Int
  certificates spelled a bare `<=`/`+` that needs `int` imported.

  Fixture, width 1, total ms (before → after): raise 9,305 → 1,266;
  line_state_start 10,128 → 1,284; times256 2,285 → 717; line_start 753 → 746;
  line_length 1,027 → 1,414; place_step 11,773 → 18,564. The chains now beat
  their hand proofs.

  `place_step` is kernel term handling, not `omega`. A `perf` profile is flat
  across allocation, `Arc` drops and `sub_tm` shifts and substitutions
  (`LocalSubst::id`, `Env::identity`). The same call gates in 0.38 s at a
  shallow depth and in ~2.5 s inside `place_step`'s binders; the hand proof pays
  5 ms because its arithmetic lives in top-level lemmas. The fix is structural:
  check the tactic's proof as a generated auxiliary lemma over only the
  variables and facts it uses. That is open for discussion.
- 2026-09-26: Scoped: lifting a tactic's proof into an auxiliary lemma. Measured by lifting
  `place_step`'s four calls by hand, width 1: the family costs 4.97 s against
  18.6 s inline (hand ~5.2 s). Closing over all of `place_step`'s parameters
  instead of a chosen few costs +1.0 s on the largest call.

  Mechanism: the kernel already has contextual globals (`GlobalBinding::Tm { ctx
  }`, referenced as `GlobalTm { var, subst }`), and proof holes use them
  (`goals.rs` `allocate`, `world`, substitution at the gate). Pushing onto Ψ
  mid-body is ruled out (lib.rs:593; every built term would shift). Proposed: a
  "proved slot" in the goal arena with Δ = `cx.gamma`, capacity from the
  existing restart loop. At the gate each slot is checked as its own opaque,
  cached item, pushed as `decl#aux_N`, and substituted as a reference rather than
  inlined. Risks: the composed renumbering at the gate, interaction with holes
  and the restart loop, and cache identity. Next: a spike for `bv_omega` only.
- 2026-09-26: Spike: lifted proofs as proved goal slots (uncommitted). `bv_omega` stores its
  checked proof in a goal-arena slot over `cx.gamma`, reserved by
  `count_holes`, so there is no restart. At the gate, `lift_proved` moves each
  slot out of the goal world into Ψ plus the earlier lifted proofs (an earlier
  one is referred to, since a `let` bound to one is inlined into what follows).
  It kernel-checks the context, statement and proof, pushes each as an opaque
  contextual global via `PendingDecl.aux`, and substitutes the slot by
  `u^id(Δ)`. The declaration's committed globals shift up past the lifted ones
  first (`shift_global_above`; a `LocalCtx` version was added to the kernel's
  subst.rs, a traversal only). The spike checks a lifted declaration inline and
  asks no cache.

  Fixture, width 1: `bv_place_step` 18,564 → 6,791 ms. The chains lost a
  little: raise 746, line_state_start 778, times256 586, line_start 539,
  line_length 651. Whole fixture ~10.1 s against the hand ~4.9 s. Default width
  and `--cache` cold and warm replay are green. Probes: `split_all` branches
  (one site, many contexts, inline after the first), a lifted proof beside a
  hole, and two lifted proofs in one body. Found beside it:
  [[omega-combo-derivation-unreconstructed]].
