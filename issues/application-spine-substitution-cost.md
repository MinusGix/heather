---
title: Type application spines and identity context references without quadratic substitution
status: closed
labels: [kernel,elaborator,performance]
created: 2026-09-26
updated: 2026-09-26
---

Typing an application spine `f(a₁, …, aₖ)` instantiates the head's Π one
argument at a time: each node returns `cod[aᵢ/x]` (`Tc::tm_infer_inner`'s
`App` rule, `AppAt`'s fast path; the elaborator's `apply_explicit` likewise).
Each step copies the *whole remaining* telescope, and after the first steps
that telescope carries copies of the earlier arguments, once per mention. A
lemma with many arguments that are themselves sizeable terms therefore costs
O(k · |telescope with arguments|) in allocation and substitution, not
O(|telescope| + Σ|aᵢ|).

A second cost of the same kind: every reference to a global in context
(`GlobalTm { subst }`, which each lifted `bv_omega` proof and each named
`omega` atom list is) runs `Tc::subst_ck`, which instantiates every context
entry's type by the prefix of the substitution, cloning that prefix per
entry. For an identity substitution in a deep context this is quadratic in
the context and checks nothing a syntactic comparison of the two contexts
would not.

## Where it showed

`bv_omega`'s word lemmas (`add_form`, `sub_form`, `bound_*`) take up to 15
explicit arguments, most of them spelled forms, each mentioned several times
in the lemma's type. After [[bv-omega-check-cost]]'s rounds cut
`bv_place_step` to its necessary `omega` calls, a frame-pointer profile of
that one declaration (library replayed) put substitution at about a third of
its time, split between the gate and elaboration's `apply_explicit`, and
`subst_ck` alone near a tenth — more than any one `omega` call.

## Shape of a fix

Both are strategy changes with no semantic content:

- **Spines**: infer the head once, walk the Π telescope collecting a
  simultaneous substitution, check each argument against its *domain* under
  the substitution so far, and instantiate the final codomain once. Only
  domains are substituted per argument. The checked-spelling recorder
  (`Spelled::Pi` per node) needs each node's Π; that is the interaction to
  cost first.
- **`subst_ck` on an identity substitution**: when `delta` is the identity on
  Γ and the target context is Γ itself (pointer or syntactic equality after
  the global shift), the judgement holds without per-entry checks.

Measure with `scripts/perf ab` on `perf/fixtures/bv_omega/` and on the
corpus: hand proofs pay the same rule, with smaller arguments.

## Log

- 2026-09-26: Landed both. `Tc::app_at_spine` walks an `app@` spine holding its arguments while the head's type stays a syntactic Π, checks each at its domain under the earlier ones substituted at once, and instantiates the codomain once; `Tc::app_at_node` is the old per-node rule, taken for a Π that needs reduction and whenever checked spellings are recorded. `apply_explicit` does the same when every node is written `app@` (the annotated `App` still needs each node's `dom`/`cod`). `Tc::subst_ck` returns at once for the identity into the current context. The identity is also materialised once per spine now, not once per node.

  Directional first (width 1, own runs, fixture uncached): subst_ck alone took `bv_place_step` ~504 → 422 ms, the kernel spine to 352, the elaborator spine to 253; the hand rows fell with it (640 → 385 ms for the six rows' hand sides), so the per-row ratios hardly moved — the rule was costing hand proofs the same way.

  `scripts/perf ab --base master` (3 samples, all separating; every counter identical except `conv_shortcut_hits` −13%, the identity references' skipped entry checks): bv fixture at width 1 wall −27%, gate −33%, max RSS −24% (`bv_place_step` gate −50%, the hand helpers −38 to −53%); showcase `calc_parser` wall −10 to −12%, gate −16 to −18%, RSS −4%. `lib/decimal_line` does not check standalone (harness module names), so it is not in the A/B.

  Tests: `crates/kernel/tests/typing.rs` `a_spine_is_typed_in_one_walk` (three-node dependent spine under a non-trivial Γ equals the annotated `app`'s syntax; an `El ⌜Π⌝` mid-spine; negative controls) and `an_identity_reference_checks_in_its_own_context_only` (identity-shaped substitution into another context still refused). Suite 3010 passed; bench --check only the known wf/check-tree band.

  Residue, not owned here: the elaborator's `lift_proved` and name resolution still substitute per use (about 5% and 3% of `bv_place_step` in the profile before this round); nothing ranks them above what `scripts/perf report` shows elsewhere.
