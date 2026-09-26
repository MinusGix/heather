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
- 2026-09-26: Landed on `bv-omega` (02b771d5): forms, bounds passed down, lifting hardened
  through the ordinary gate, cache and pool; `bitvec_omega` hand-proved. Suite
  green. Fixture, width 1: `bv_` rows total ~10 s against ~4.9 s hand.

  What is left is `omega`'s own certificates. Literals, kernel steps (width 1):
  `List<Nat>` 1 element ~430, 50 elements ~580; `List<Int>` 1 element ~700,
  50 elements ~4,200; a lone Int literal 44; a Nat literal 0. An identity lemma
  applied to variable lists costs 0 steps, to literal lists ~3k. So a list costs
  a fixed amount per occurrence (probably decoding `List`'s encoded type each
  time, unconfirmed), and omega's certificates carry about ten literals per
  lemma application. Two ways, complementary: make `List` literals cheap (a
  kernel memo of the decoded type; general), or list-free omega certificates
  (constraints as Nat forms `P ≤ Q`, combination by `form_*` steps; also removes
  Int evaluation). Next: profile a list-heavy check before choosing.
- 2026-09-26: List profile: the per-call overhead is omega certificates re-spelling their atom list (177 copies of a six-atom list, ~145k of 152k kernel steps on one small goal); owner [[omega-certificate-atom-list-repetition]]. Per-constructor costs: `Nil` ~43, `Cons` ~85, an Int literal ~44; a list literal lowers through a `Vec` fold, ~430 steps whatever its length.
- 2026-09-26: Attribution after the atom list was named (c26e5d46).

  **Elaboration** (`bv_raise_value`, ~450 ms of body outside every omega timer).
  Two probe sessions that elaborated each fact's word a second time, in a
  cloned `Elaborator`, whose clone also copies the attempt's notes:
  - Operator dispatch (`op_carrier_head`) infers an operator's left operand in
    a probe to find its carrier, and in `t.toNat() + Q` that operand is a whole
    word. `bv_omega` now spells its arithmetic as qualified calls
    (`nat::Nat::add`, `mul`, `Lt`, `Le`), as `omega`'s certificates already
    do. Refusals still quote the operator spelling (`Obligation::shown`).
    `logic::And(…)` does not read as a type, so `∧` stays; it is type syntax,
    not dispatch.
  - An equation's direction probe (`type_endpoint_may_need_checking`) walked
    into an application's head. A bare `bitvec::BitVec::toNat` has a leading
    implicit, so it counted as checking-only and sent every fact over a
    `toNat` to the semantic probe on both endpoints. The walk now skips
    application heads; the application is judged whole, as `is_checking_only`
    already does. Skipping heads alone broke `lib/elf64_io.hthr`: an equation
    whose left side is a motive-less `match` had been checked right to left
    only because the walk tripped on `Some`'s head. A motive-less `match` now
    counts as may-need-checking in its own right, and the probe decides.

  Kernel counts identical, so the terms are unchanged. `scripts/perf ab`
  (width 1, 3 samples, loaded machine): per item every sample separates,
  `bv_raise_value` 686–963 → 250–353 ms, `bv_line_state_start_value` 771–902 →
  293–332 ms; the `bv_` rows sum 3.8–5.4 → 2.5–3.2 s. The file totals overlap
  (−21% median, not a result). Suite: 2998 passed.

  **Gate.** `bv_place_step`'s 268k steps are mostly its ~12 `omega`
  certificates. In one certificate (the 24k-step `om1` item), one conversion is
  53.8 ms of the ~78 ms gate. It is the last step, `le_trans(lower,
  dot(ROW, A), upper, …)`, where `ROW` is the root fact's row and the lower
  bound's proof states its row as the whole derivation, `scale(-1, combo(…))`.
  Equal as coefficient lists, spelled apart, so the checker evaluates the
  derivation's row. Probe: `ROW = derived` by `refl`, no atoms involved, is
  13.6k steps and 60 ms alone. So the cost is evaluating roughly ten nested
  `combo`/`scale`/`add_coeffs` over six-element rows: in-language Int
  arithmetic over the encoded `Int`, tens of steps per operation (a lone
  `Int::mul` of literals, with its literal types, ~300 steps per theorem; Nat
  literal arithmetic is native, ~20). A derivation that is a DAG is spelled as
  a tree, so shared rows are evaluated once per occurrence.

  Refuted along the way, each with a probe: negative combination scales spelled
  `NegSucc` against the lemmas' `-b` (no change in misses); strict facts
  converted `Lt` against `Le` (−1.3% steps; 13 such steps cost 0.1 ms each);
  a literal against a computed bound (4.5 ms gate for 13, either way).

  Levers, by where the cost is:
  1. **Cheaper Int evaluation**: kernel-native Int literals and operations,
     as Nat has. The biggest lever, and a kernel change.
  2. **Rows evaluated once**: `have`-bind each derived row's literal
     coefficient list with a `refl` proof, so the final comparison is between
     literal rows. Last time literal rows doubled the cost through list
     checking; with the atom list named that may no longer hold, since a row
     is now the list the checker meets.
  3. **Rows as Nat pairs or forms**, the list-free certificate idea: no Int at
     all.
- 2026-09-26: Probe of lever 2 (rows evaluated once): refuted. Each derived row
  named by a transparent slot holding its literal coefficient list; each bound
  moved onto the name by `lower_along`/`upper_along`/`exact_along` with a
  `refl` (env-gated, reverted). On the 24k-step `om1` item the single 57 ms
  final conversion disappears, but ~30 `refl` steps at 5–8 ms take its place.
  Conversion-miss time is unchanged (63.6 → 64.4 ms), and kernel steps double
  (24.3k → 47.3k) with the literal lists' own checking. The derivation was
  never evaluated twice: the cost is per operation.

  The heaviest `refl` involved no big coefficients: `sub_coeffs` of a
  normalised fact's rows, a handful of list operations over six elements of 0
  and 1. Scaling probe, `sub_coeffs(x, y) = z` by `refl` over literal rows:
  6/12/24/300 elements cost 1.5k/3.0k/5.8k/72k kernel steps, ~245 per element
  (two `Int::mul`, one `Int::add` and the list matches), ~0.65 ms per element.
  δ-unfolds are ~15 per element, selections 0. Checking a literal
  300-element `List<Int>` is itself ~126 steps per element. Profile of the
  300-element case: conversion's normalisation of values *with their types*
  (`tm_nf`/`ty_nf`/`ty_root` over the encoded constructors' annotations),
  η-projections on Σ-encoded children, local shifting, and the allocation and
  dropping of the terms and types that produces. So an encoded `match` or
  constructor costs tens of steps, whatever the numbers.

  This makes the kernel lever the next one, and a general one: cheap evaluation
  and comparison of encoded inductive values (constructor annotations not
  re-normalised per node, children not η-expanded per projection), which
  `Int` and `List` would both get, not an `Int`-only primitive.
