---
title: bv_omega costs several times the hand proofs it replaces
status: open
labels: [performance,proofs,bitvec,omega]
created: 2026-09-26
updated: 2026-09-28
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
- `decimal_line` adopts the tactic for the facts where it is then within the hand proofs' cost (the table in the parent's log is the baseline). Amended 2026-09-27: it adopted the tactic for every row, `place_step` included, as a matter of dogfooding. This issue now owns the remaining gap, not the adoption.

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
- 2026-09-26: The generic per-value cost found while costing a kernel mechanism for `Int`-shaped values was the nominal tag, not the kernel: a Σ-of-`Unit` binary nest that Σ-η walked on every comparison of declared-inductive data. It is now `sEq⁰(Nat; k; k)` ([[nominal-tag-conversion-cost]]). This fixture: eval_steps −30.9%, gate −11.9% (`bv_place_step` 1.101 → 0.971 s at width 8); `lib/std/omega` gate −15.4%. The bar is still not met; what remains per element is evaluation of the encoded operations (`match` on `Int`, the `fst(snd^j)` projections, `List` cells), which is where a packed-constructor representation would act.
- 2026-09-26: Remeasured after [[nominal-tag-conversion-cost]]. The remaining per-element cost of omega's rows was not evaluation proper: every `elim_Wf` β rebuilt its induction hypothesis's syntax, shifting the recursor's whole step body per list cell ([[wf-ih-rebuilt-per-node]], now native). Fixture gate −54% (`bv_place_step` 1.05 → 0.28 s). Against the bar, width 1, min of two runs: the six `bv_` theorems total 1.33 s, the 24 hand-side theorems (rows plus their helpers) 0.41 s — 3.2×. Both sides got faster, and the hand side, which also runs `omega` and list lemmas, got faster by more, so the ratio is worse than the earlier ~2.4× although `bv_omega` itself is several times cheaper than this morning. The bar is not met; the next attribution is per `bv_` row against its own hand row plus helpers.
- 2026-09-26: Per-row attribution (width 1, min of two runs; a row's hand side is its hand theorem plus everything it uses, shared helpers included since the chains build on each other): times256 104 ms hand / 86 bv (0.8×, meets the bar); raise 147 / 222 (1.5×); line_state_start 162 / 242 (1.5×); line_start 25 / 101 (4.0×); line_length 22 / 120 (5.5×); place_step 232 / 555 (2.4×). The gap is mostly gate for place_step (267 vs 117 ms) and the line facts (61 vs 12, 68 vs 11), and elaboration for raise (decl body 117 vs 27 ms).

  Line facts: half of `bv_line_start`'s gate was one conversion (31 ms), the leaf fact `toNat(w) + 0 = 1 * toNat(w) + 0` checked against `form_atom`'s `a = 1 * a + 0`. `a + 0` reduces in one step, but `toNat` is the newer head, so conversion unfolds the word first. New lemma `bitvec_omega::form_leaf` states the leaf in the facts' own shape. perf ab vs 37b8d094: `bv_line_start_value` gate −58%, `bv_line_length_value` −38%, fixture gate −5.2%, eval_steps −8.3%; no row slower. Suite green.

  Next suspects, not yet measured: the word bound `pow(2, 64)` exceeds a `u64` literal, so `omega` spells it as a byte chain and the kernel computes with it as a composed run — an `omega` goal against it cost 2× the steps of the same goal against 2^60 in a micro-probe (the hand proofs bound by 2^60). place_step: gate, the elaboration-side certificate check (141 vs 81 ms) and body elaboration (88 vs 9 ms) are all larger than the hand lemmas'. raise: form elaboration.
- 2026-09-26: The `pow(2, 64)` lead, tested and set aside. A micro-probe had `Lt(x, pow(2, k))` at ~2.2k kernel steps for every k (60 as much as 65) against 48–114 for the same comparison with a literal, because the kernel folds `pow` one multiplication per exponent step; and an `omega` goal against 2^64 took 2× the steps of one against 2^60. Restating the word lemmas over a supplied `top` with `ht: 2^n = top`, proved once per call, and spelling every bound as the literal (omega's own byte form past `u64`) moved the fixture's `bv_` rows by only −2 to −6% in steps and nothing outside noise in time. Reverted, not landed. The reason: steps are not time here. Native word operations charge one step per bit, so words and powers inflate step counts cheaply — an `omega` with a word atom took 8.3k steps against 3.6k with a variable atom, at the same 4.3 ms of gate.

  Where `bv_line_length`'s time actually goes (its generated proof lifted into standalone theorems, width 1): the word-lemma pieces (`ofNat_form`, `form_leaf`, `sub_form`, the range) cost ~0; the row is its `omega` calls — the generated goal (24 ms total), one side condition (13 ms), and the trailing `omega` the fixture row writes itself (30 ms, it handles a truncated `5 - line_skip(n)`). The hand proof makes no `omega` call. A trivial two-atom `omega` costs ~4 ms of gate plus ~4 ms of elaboration. So the remaining gap is the number of `omega` calls times omega's per-call floor, not word handling. Levers: fewer calls per `bv_omega` (the goal and each side condition are separate calls), a cheaper certificate for small problems, and a `bv_omega` that proves the subtraction itself so the row needs no trailing `omega`.
- 2026-09-26: Omega calls cut. A temporary dump of every generated proof showed each `bv_omega` making 2–3 top-level `omega` calls (the goal, one per side condition) and `bv_place_step` making 12, three of them the careful pre-check of a restated fact's new side conditions (`holds`), which the bundle then proved again. Most calls had their answer written down already. Now:
  - **Goal read off a fact**: a goal `toNat(t) = r` whose `r` reads as `t`'s form `P` (with `Q` zero), or `toNat(t) = a - b` with `a`, `b` reading as `P`, `Q`, is `fact_value`/`fact_diff`, no `omega`. So `bv_line_length` proves its truncated difference directly; the fixture row drops its own trailing `omega`.
  - **Leaves defined by facts**: `toNat(t) = v` in scope states the leaf over `v` (`leaf_value`), so `zeros: leading_zeros(…).toNat() = line_skip(n)` puts `line_skip(n)` into the forms and the goal matches. Still a leaf for the goal over Nat variables (generalising it restated its fact as a duplicate and grew `place_step`'s `omega` problems).
  - **Stated bounds**: a fact `x < k`/`x <= k`, `k` a literal within the width, `x` of the word's form, is the word's bound (`below_top`, `below_top_le`; the kernel decides `2^60 <= pow(2, 64)` in ~2k steps).
  - **Closed side conditions** by `trivial`.
  - **Optimistic restating**: facts restated untried; on refusal, the careful proof (arena rolled back: a refused attempt and each `holds` probe had left their named atom lists in the goal arena).

  Calls per row: times256 2 → 0, raise/line_state_start 2 → 1 (goal direct, bound by `omega`), line_start 2 → 1, line_length 3 + the row's own → 1, place_step 12 → 6.

  `scripts/perf ab --base HEAD` on the committed fixture (old line_length row, which both binaries prove; width 1, 3 samples): file gate −10.3% and total −8.8%, both separating; eval_steps −11.4%. Gate per row, separating: line_start −77%, times256 −74%, line_length −21%, line_state_start −15%, raise −6%; place_step −23% overlapping. Hand rows unchanged. Suite 3008 passed; bench --check only the known wf/check-tree band.

  Bar, width 1, min of two runs, new fixture: times256 0.25×, raise 1.46×, line_state_start 1.31×, line_start 1.32×, line_length 1.37×, place_step 2.18×; rows total 1.48×. Five of six rows meet 1.5×. place_step does not, and it is no longer `omega`: its six calls cost about what they cost as standalone lemmas (context-free probes: no in-context premium). A frame-pointer profile of that declaration alone puts about a third of it in substitution — application spines instantiating the whole remaining Π per argument over the word lemmas' 15 spelled-form arguments, and `subst_ck` on every in-context slot reference — filed as [[application-spine-substitution-cost]].
- 2026-09-26: [[application-spine-substitution-cost]] landed: fixture wall −27%, gate −33% at width 1, but the hand side fell with the bv_ side, so the bar is where it was — five rows within 1.5×, place_step ~2×. What separates place_step from its hand proof is now neither omega calls nor substitution; re-attribute before the next round.
- 2026-09-27: `place_step` attributed once more (width 1, fixture, two runs within 5%; temporary per-call and per-`omega` prints, reverted). `bv_place_step` 243 ms against 122 ms for the hand `place_step` plus the twelve helpers it uses (2.0×). By phase the gap is `decl_body` +50 ms, gate +39, the `omega_*` phases +21, `elab_whnf` +7. Per `bv_omega` call (elaboration, inclusive): `under` 13 ms, the kept branch's goal 22, `over` 12, `sum` 53. The outermost `omega` checks sum to 68 ms over six calls, against 43 ms over the hand side's nine.

  Why each `omega` costs more: every hand helper states only the facts its one `omega` needs, so its problems have 5–6 atoms and 8–10 assumptions. `bv_omega`'s calls run in the declaration's context, with 7–8 atoms and 17–20 assumptions. The certificates are already pruned: `kept_under`'s uses `value`, `low`, `parts`, `remainder`, and `bv_omega`'s first call uses the same four plus its own `__bv_h1`. So the cost is not unused facts. It is the width of every coefficient vector (one entry per atom, `w` included because `low` needs it) and the extra equation per generalised word (`__bv_w1`, `__bv_h1: w1 + 0 = P`). There is also duplicated work: calls 1–3 each rebuild the same fact for `ofNat(1099511627776 * c)` (`below_top`, `ofNat_form`, the form chain).

  Levers, not taken: (a) where a word's `Q` is zero, put its form `P` straight into `omega`'s goal instead of generalising it. That saves one atom and one equation per such word, at the price of transporting the goal along the fact. (b) Share word facts between the `bv_omega` calls of one declaration (a slot, like `omega`'s atom list). (c) Pruning atoms that are reachable only through unused facts does not help here. Together, (a) and (b) would recover part of the gap. The rest is structural: a hand proof split into single-purpose lemmas gives `omega` minimal contexts, which a tactic working in place does not get. Verdict: `place_step` stays at about 2×, and the library switches to `bv_omega` anyway (dogfooding over hand proofs). The levers above are this issue's remaining work.
- 2026-09-27: `lib/decimal_line.hthr` switched. `times256_value`, `raise_value`, `line_start_value`, `line_length_value`, `place_step` and a new `line_state_start_value` (split out of `line_word_value`) are now `bv_omega`, and 12 helpers are gone (`double_value`, `double_scaled`, `doubling_bounds`, `raise_bounds`, `kept_*`, `taken_*`, `weight_small`). `bitvec_omega` is bundled before `decimal_line` in `PRINT_SUPPORT` and in `read_print_process.rs`. A trap found on the way: `line_state_start_value` with no fact in scope took `raise` apart down to its 40 doublings (161 ms). With `raise_value`'s fact in scope, `raise(x)` is a defined leaf (15 ms). So state a proved sub-word's value before calling `bv_omega`. Staged standalone check at width 1, per-module item totals over two runs each: `decimal_line` 1.45 s → 1.69 s (+17%), gate 0.57 → 0.64 s; `bitvec_omega` itself 16 ms. Largest remaining row: `raise_value` (~150 ms, forty doublings taken apart), owned by [[bv-omega-definition-summaries]]. Full suite 3010 passed; `wc_l_prints_what_the_read_returned` 50 s wall with the library half cold.

- 2026-09-28: Adopted the byte and comparison bridges from
  [[bv-omega-bytes-and-comparisons]] in `decimal_line`. `place_step` now
  proves its `True`/`False` outcomes directly with `bv_omega`; its separate
  Nat orders and `unsigned_lt_nat` transport are gone. `word_bytes_of`
  uses a width-generic `byte_parts` lemma proved by two `bv_omega` calls,
  returning the low byte's word equality and the high part's Nat value.
  This removes seven explicit `toNat_take_drop` proofs, their range
  arguments, and seven applications of `byte_of_value`. The remaining
  `byte_of_value` is itself `bv_omega`.

  Factoring is load-bearing. Eight independent `bv_omega` arguments to
  `eight_cong` checked, but their row cost 10.64 s total / 5.53 s gate in a
  single width-one probe, against the old byte row plus helpers at
  0.133 s / 0.053 s. Factoring the seven splits but leaving the last byte
  inline still cost 1.576 s / 0.604 s for the row: its written alias is not
  the canonical drop term in the helper's result, so the walk retraverses
  the extraction chain. Passing that result to `byte_of_value` keeps the
  last tactic call in a small context too. `below_value` retains its
  Boolean-to-Boolean guard transport: the new tactic bridges constant
  outcomes, and replacing its two direct value lemmas with tactic calls
  doubled that small row's cost in the probe without simplifying the proof.

  Measured against `08d647ad`, one release binary (SHA prefix
  `55101045451a`), local Ryzen 7 5700X, kernel width 1, three interleaved
  cold samples through `scripts/perf ab --source-patch`. Current kit,
  model, fetch and store modules were staged in
  `target/decimal-line-comparisons/` under their import names; standard
  modules came from `lib/std`. Medians, item rows only:

  | rows, including their helpers | total ms before → after | gate ms before → after | evaluator steps before → after |
  |---|---:|---:|---:|
  | `place_step` | 489.7 → 459.4 | 152.8 → 160.2 | 190166 → 187511 |
  | bytes (`word_bytes_of`, old `byte_split` / new `byte_parts`, `byte_of_value`) | 130.3 → 173.4 | 52.9 → 56.6 | 80631 → 91287 |
  | all `decimal_line` items | 2266.3 → 2247.5 | 824.3 → 778.1 | 622663 → 630664 |

  The time sample ranges overlap in every row group: no speedup or slowdown
  claim. The module pays 1.3% more evaluator steps and 4.8% more global
  rescoping nodes (2062771 → 2162477); the byte group pays 13.2% more steps.
  Whole-file wall medians, imports included, were 6.06 → 5.72 s with
  overlapping samples too. Verdict: substantially less proof plumbing at
  approximately the same observed whole-module cost; retain the shared
  lemmas rather than independent byte proofs. Raw tables and the replayable
  report are in `target/perf-ab/`; the group summary is
  `target/decimal-line-comparisons/summary.json`.

  Reproduce the source measurement after saving the library diff to a patch:
  `scripts/perf ab --source-patch /tmp/decimal-line-bv-simplification.patch
  --heather target/release/heather --file
  lib/decimal_line.hthr:lib/std,target/decimal-line-comparisons --only
  lib/decimal_line.hthr --samples 3 --kernel-workers 1 --cpu-secs 300`.

  Validation: the full formatter passed the release CLI kernel check;
  `scripts/test -p heather-elab --test read_print_process` passed its print
  certificate acceptance and twelve mutation refusals; `scripts/test -p
  heather-cli --test native_read_loop -- wc_l_prints_every_line` passed
  certificate generation and execution, including fragmented input and
  failed reads/writes. Both ran in the normal lane.
