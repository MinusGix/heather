---
title: Wf former: finitary branching inductives in the kernel
status: open
labels: [kernel,inductives,metatheory]
created: 2026-07-25
updated: 2026-07-25
---

The kernel round for route C of [[tier1-branching-constructors]]: three
formers (`Vec`, `Fin`, `Wf`) giving finitary branching inductives with
Σ-tuple children and a `Fin`-indexed ih. **Rules:**
`docs/wf-former-design.md` (written before the code, still the spec the
implementation is checked against). **Decision record:**
`docs/branching-inductives-choice.md` §15. **Kernel summary:**
`crates/kernel/DESIGN.md`, Fragment section, last two paragraphs.

## Status: phases 1–4 landed, phase 5 is next

| | Phase | State |
|---|---|---|
| 1 | `Vec` + `Fin` formers | **done** — commit `f538141`, `crates/kernel/tests/vec_fin.rs` (12) |
| 2 | `Wf` / `sup_f` / `elim_Wf` | **done** — commit `2ddd20b`, `crates/kernel/tests/wf.rs` (12) |
| 3 | codes + `rec.rs` branches; lifts the layer-c gate | **done** — commit `1c43729`, `crates/kernel/tests/wf_codes.rs` (8) |
| 4 | ch. 07 logical relations | **done** — `docs/metatheory-ch07-extensions.md` part II. **Abort criterion not triggered.** One kernel defect found and fixed |
| 5 | generator round (one regime) | **next** — closes [[tier1-branching-constructors]] |

**The falsifier is spent and the decision is final.** Route A is no longer a
live fallback; `crates/elab/tests/branching_route_a.rs` stays only as the
costed record of what was not taken. Do not reopen
[[branching-inductives-decision]] without new evidence of a *different* kind.

Full suite is at **311 passing**. Run it with `scripts/test` (never bare
`cargo test` — see CLAUDE.md); note that `scripts/test` now sets
`RUST_MIN_STACK=8M`, because checking the `tm_elim_wf` branch of a
45-branch recursor recurses deeper than the 2 MiB default test-thread
stack allows.

## What exists now

- `Type::Vec { level, elem, len }`, `Type::Fin { len }`,
  `Type::Wf { level, shape, arity }`; `Term::Supf`, `Term::ElimWf`; the
  codes `Term::TmVec`, `Term::TmFin`, `Term::TmWf`.
- `term::nth(level, elem, len, cs, idx)` — the fixed `elim_Nat` schema, not
  a former; materialized by the `Wf` rules.
- `term::wf_step_telescope(gamma, level, motive_level, shape, arity,
  motive) -> (cs_ty, ih_ty, step_ty)` — built once and shared verbatim by
  `typing.rs`, `conv.rs`, `rec.rs` and `reduce.rs`, deliberately, so the
  four transcriptions of the step telescope cannot drift.
- **No layer-c gate any more**: all three formers, `sup_f`/`elim_Wf` and
  the three codes are layer-c citizens, and the code recursors carry all
  eight new branches (`ty_vec`/`tm_vec`, `ty_fin`/`tm_fin`, `ty_wf`/
  `tm_wf`, `tm_supf`, `tm_elim_wf`; 37 → **45**), so boxed code is still
  exhaustively recursable.

## Phase 4: the falsifier, spent

Full argument: `docs/metatheory-ch07-extensions.md` §§10–17. What phase 5
and any later reader need from it:

- **`Vec`/`Fin` have no LR case at all** — stronger than predicted. Type
  rules are keyed on the whnf; canonical lengths reduce away (weak-head
  expansion inherits the `Unit`/`Σ`/`Empty`/`+` clause) and neutral lengths
  hit the existing neutral-type rule. They owe two Congruence-for-Neutrals
  laws, of a new kind: the first neutral-type congruences with a *type*
  premise (`El ν`'s premise is a term).
- **`Wf` is a restriction of `W`'s in three senses** — type rule (a `Nat`
  term relation where `W` has a position-*type* relation), term relation
  (finite Σ-spine where `W` has a subtree quantifier), layering restriction
  (one contravariant premise where `W` has two). `NfEqWf` is a `Wf`-shaped
  inductive definition where `NfEqW` is a `W`-shaped one.
- **The spine recursion is on the arity's `NfEqNat` derivation, not on
  either length.** The two sides' arities are related, not equal; `NfEqNat`
  is what forces them to reduce in lockstep. This is the one place a
  careless copy of `W`'s clause goes wrong.
- **One new lemma**, the index lemma (§13): `elim_Wf`'s arm needs
  relatedness at arbitrary `Fin` indices, which the finite spine does not
  hand over. Four cases, all reductions the kernel already performs.
- **No funext obligation in the `elim_Wf` arm.** The only `Π` is the ih and
  the `Π` term relation is the applied form — the semantic counterpart of
  "the ih is transient".

### The kernel defect it turned up

`Vec^l(T; 0) ⇝ Unit` **dropped the level**: a well-formed
`Π^{1,0}(_ : Vec^1(T;0)). Nat` stepped to an ill-formed
`Π^{1,0}(_ : Unit). Nat`, i.e. type-level subject reduction failed for every
`l ≠ 0`. Invisible until now because a generated shape is a sum of records
at level 0, so every test and prototype sat at `l = 0`.

Fixed: `Unit` and `Empty` are **level-polymorphic** in formation
(`typing.rs::ty_check` special-cases them; `ty_infer` still reports `0`, now
documented as the *least* level). Not cumulativity — every other former
keeps an exact level, and `Vec` only ever over-declares. Regressions in
`crates/kernel/tests/vec_fin.rs`. Recorded in `crates/kernel/DESIGN.md`.

The rule of thumb worth carrying: *a former with no components has nothing
bounding its level from below*, and `Vec` is the kernel's first type former
whose whnf is chosen by a term that does not carry a level of its own —
`El`'s term is a code and does.

## Findings from phases 1–3 worth not rediscovering

- **The `Vec`/`Wf` branches bind one universe, not two.** `ty_w`'s shape
  and positions are both types, so it binds `ℓ, ℓ'`; an arity is a `Nat`
  term and contributes no level, so `ty_vec`/`ty_wf`/`tm_vec`/`tm_wf` bind
  only `ℓ`, and `ty_fin`/`tm_fin` bind none. Copying `ty_w`'s dims verbatim
  is the mistake to avoid.
- **A type-motive branch can have a term-motive recursive call.** In
  `ty_vec`/`ty_fin`/`ty_wf` the length/arity recursion goes at the *term*
  motive (`ty_el` is the ch. 04 precedent), so their `BRANCH_DIMS` entries
  end `(…, false, false)`: `Var(0)` does *not* inhabit the branch type.
- **Deep telescopes cost stack.** The `nth` schema inside
  `wf_step_telescope` made the 45-branch recursor check overflow the 2 MiB
  test-thread stack; `scripts/test` now sets `RUST_MIN_STACK=8M`. If
  elaboration ever runs recursors over deeply nested code, the same limit
  applies there.
- **Generated proof-irrelevant types break "η is not blind" negatives.**
  Adding `Vec` to `crates/kernel/tests/common/wt.rs` made
  `sigma_eta_and_neutral_distinctness` fail: `Vec(T;0) ⇝ Unit`, so a Σ of
  such components really does identify its inhabitants — the kernel was
  right. That negative now runs at `Σ(S, Nat)`, relevant by construction.


- **The motive is an ordinary `Type` binding `z`** — no `Ty`-code round
  trip. The postulate prototypes needed codes because their eliminator was a
  term with a `Ty`-valued motive; a real former does not, so the generated
  recursor (phase 5) is simpler than
  `crates/elab/tests/branching_route_c_nary.rs` suggests.
- **`Empty`-η is not needed for the nullary arm**, contrary to what the
  route-A round implied. Arity 0 is `Vec(T; 0) ⇝ Unit`, and proof
  irrelevance already collapses every nullary constructor form — including
  the `u : Unit` payload in the tag. `Empty`-η stays independently nice for
  tier-2 `Acc` under `W`, but nothing here depends on it.
- **`Fin` was the sheddable piece** if phases 3–4 ran heavy: it never
  mentions `Wf`, so it could revert to an inlined `El (elim_Nat …)` schema
  (the n-ary prototype did exactly that and it worked). Neither round needed
  it — phase 4 gave `Fin` no LR case at all, which is the cheapest possible
  outcome — so it stays primitive, for goal readability and symmetry.
- **`Rose`-style nesting falls out of arity-as-a-term**: `Rose { Node(A,
  List Rose) }` is `Wf` with `S = Σ(a : A). Nat` and `n = snd x` — the child
  list *is* the `Vec`, its length is data in the shape. Worth exercising in
  phase 5.
- Watch de Bruijn indices in hand-built test terms: `App`'s `cod` binds its
  argument, so it sits one level deeper than the ambient. Both acceptance
  tests failed first on exactly that — in the test, not the kernel.
- **Level 0 hides level bugs.** Everything the generator produces sits at
  level 0, so a former whose reduction mishandles levels looks correct
  through the whole test suite. Phase 4's defect needed `Vec^1` to show.
  Worth a deliberate `l > 0` case in phase 5's exercises.

## Also in scope, decision-independent

`Empty`-η in `conv.rs` — cheap, plainly sound, improves the tier-2 `Acc`
story regardless of anything above. Not blocking.

## Log

- 2026-07-25: Phase 1 landed — Type::Vec and Type::Fin in the kernel. Reductions on the length (Vec(T;0)⇝Unit, Vec(T;S k)⇝Σ(_:T).Vec(T;k), Fin(0)⇝Empty, Fin(S k)⇝Unit+Fin(k)), neutral at a neutral length with structural congruence there; formation rules (Vec at its element's level, Fin at 0, length checked at Nat); no introduction/elimination forms — all eta is inherited through the reductions, which is the design's whole premise. Sites touched: term.rs (enum), subst.rs (length at same depth, no binder), reduce.rs (step_type + is_whnf_type/is_neutral_type keyed on whether the length is stuck + explicit beta_elim_ty block), typing.rs (formation + not_code_layer gate), conv.rs (neutral-length congruence + tm_nf neutral-type arm), fmt.rs. GATE: Vec/Fin are rejected at layer c until phase 3 gives them code formers and rec.rs branches, so boxed code stays exhaustively recursable; beta_elim_ty returns None (stuck) rather than mis-firing as belt-and-braces. Tests: crates/kernel/tests/vec_fin.rs (12), including sigma_eta_reaches_through_vec — for a NEUTRAL tuple cs : Vec(Nat;2), cs is convertible with its own projections repackaged, i.e. the equation route A needs funext for, discharged here by existing Sigma-eta + Unit-irrelevance. Also added Vec/Fin to the property-test type generator (common/mod.rs arms 16/17, >20/300 hit rate verified by test), so subst_laws/conv_properties/reduce now exercise them; full suite 289 passing.
- 2026-07-25: Phase 2 landed — Wf, sup_f, elim_Wf. Formation (Wf^l(x:S).n at level l — the arity is a Nat TERM with the shape free, so it contributes no level, unlike W whose positions are a type), introduction with Vec-tuple children, dependent elimination with the Fin-indexed ih, and the beta rule that synthesizes the ih lambda around the recursive call (same 'only beta rule that builds a binder' shape as elim_W's, but over a Fin index). nth is NOT a former: it is a fixed elim_Nat schema materialized by the rules (term::nth), and the step telescope is built once in term::wf_step_telescope and shared verbatim by typing.rs and conv.rs so the two transcriptions cannot drift — the hazard the design doc flagged. Sites: term.rs, subst.rs (arity binds one, motive one, step three), reduce.rs (beta + neutrality + whnf), typing.rs, conv.rs (Wf type congruence, sup_f value comparison at Vec type, elim_Wf neutral congruence), fmt.rs, tests/common (count + generators). Still layer-c gated until phase 3. ACCEPTANCE MET (crates/kernel/tests/wf.rs, 12 tests): Tree { Leaf, Node(Tree,Tree) } built on the real former, and mirror (mirror t) = t proved with every beta-marker deleted — the Leaf arm is literally refl_tree(leaf()) and the Node arm is cong + cong + trans, versus route A's funext-per-arm. sigma_eta_bridges_the_constructor_form pins the headline at the real former: for a NEUTRAL tuple cs, sup_f(inr u; cs) is convertible with node (nth 2 cs 0) (nth 2 cs 1). Two notes for phase 3: the motive is an ordinary Type binding z (no Ty-code round trip, unlike the postulate prototypes, since the eliminator is a former now), and Empty-eta turned out NOT to be needed for the Leaf arm — arity 0 is Vec(T;0) which reduces to Unit, whose proof irrelevance already collapses every nullary constructor form. Full suite 301 passing.
- 2026-07-25: Phase 3 landed — codes and the eight recursor branches; the layer-c gate is gone. New codes Term::TmVec/TmFin/TmWf with El decoding (only the element/shape decodes; the length and the arity are Nat terms and ride across unchanged). New branches ty_vec/tm_vec (1 univ, 3 globals, 2 locals), ty_fin/tm_fin (0/2/1), ty_wf/tm_wf (1/3/2), tm_supf (1/5/4), tm_elim_wf (2/6/5) — the last comparable to tm_elim_w but one universe shallower, its step binding built by wf_step_telescope so rec.rs/typing.rs/reduce.rs share one transcription. Sites: term.rs (3 variants + 8 Branches fields), rec.rs (branch_terms/branch_specs 37→45), subst.rs (code depths + map_branches), reduce.rs (El decoding, beta_elim_ty Vec/Fin/Wf replacing the None gate, beta_elim_tm TmVec/TmFin/TmWf/Supf/ElimWf, whnf classification), typing.rs (TmVec/TmFin/TmWf rules; not_code_layer deleted outright — it had no other users), conv.rs (congruence for the three codes), fmt.rs. Tests: crates/kernel/tests/wf_codes.rs (8) — El decoding, layer-c acceptance, and the identity recursor round-tripping box(Vec), box(Fin), box(Wf), box(TmVec/TmFin/TmWf), box(sup_f) and box(elim_Wf) in one β-step, which is the sharp cross-check of the new telescopes against reduce.rs's fire; plus a poisoned-branch negative and a generator-coverage check. BRANCH_DIMS is 45, identity_branches (both copies) grew eight hand-written arms, and both generators now reach the new formers — the scope-only one in common/mod.rs and, new here, the well-typed one in common/wt.rs (Vec/Fin/Wf types and TmVec/TmFin/TmWf encodings), so the subject-reduction and identity-recursor property suites cover them. Two incidental fixes fell out: scripts/test needs RUST_MIN_STACK=8M for the deeper telescope, and conv_pair_properties' 'η is not blind' negative moved to Σ(S, Nat) because a generated Vec(T;0) is genuinely proof-irrelevant. Full suite 309 passing.
- 2026-07-25: Phase 4 landed — the ch. 07 pen-and-paper pass, `docs/metatheory-ch07-extensions.md` part II (§§10–17). ABORT CRITERION NOT TRIGGERED; the branching-inductives decision is final and route A is no longer a live fallback. Vec/Fin turn out to need NO logical-relations case at all (stronger than the design doc's §8 prediction of "restricted clauses"): every type-relation rule of 07 is keyed on the whnf, so at a canonical length they reduce away and weak-head expansion inherits the Unit/Σ/Empty/+ clause, while at a neutral length they ARE the whnf and the existing neutral-type rule applies — they owe only two Congruence-for-Neutrals laws, which are a new kind (first neutral-type congruence with a type premise; El ν's premise is a term). Wf's case is a restriction of W's in three separately checkable senses: its type rule is W's with a term relation at Nat replacing the position-type relation F; its term relation NfEqWf replaces W's subtree quantifier with a finite Σ-spine, recursing on the arity's NfEqNat derivation (NOT on either length — the two sides' arities are related, not equal, and NfEqNat is what forces lockstep reduction; this is the one place a careless copy of W's clause goes wrong); and its layering-restriction case has one contravariant premise where W has two. Consequence worth keeping: NfEqWf is a Wf-shaped inductive definition where NfEqW is a W-shaped one, so a mechanization needs only finitary branching induction where W needs infinitary — the object-level restriction holds one level up too. The single new obligation is the index lemma (§13): elim_Wf's arm needs relatedness at arbitrary Fin indices, which the finite spine does not hand over directly; four cases (arity ze/su/neutral, and NfEqSum on the index), all reductions the kernel already performs, all at an arbitrary weakening because the children premise stays Kripke-quantified. No funext obligation appears in the elim_Wf arm: the only Π is the ih and the Π term relation is the applied form, the semantic counterpart of "the ih is transient". KERNEL DEFECT FOUND AND FIXED, and it is the pass paying for itself: writing the fundamental-theorem arm for Vec-formation exposed that Vec^l(T;0) ⇝ Unit DROPS THE LEVEL, so a well-formed Π^{1,0}(_ : Vec^1(T;0)). Nat stepped to an ill-formed Π^{1,0}(_ : Unit). Nat — type-level subject reduction failed for every l ≠ 0. Invisible until now because a generated shape is a sum of records at level 0. Fixed by making the two component-free formers (Unit, Empty) level-polymorphic in formation: typing.rs::ty_check special-cases them ahead of the level comparison, ty_infer still reports 0, now documented as the LEAST rather than the canonical level. Not cumulativity — every other former keeps an exact level and Vec only ever over-declares (successor preserves l, nullary drops to 0), so nothing large enters a small universe; conv.rs needed no change since ty_nf already ignores its level argument. Two regressions in crates/kernel/tests/vec_fin.rs (vec_at_zero_reduces_without_dropping_its_level, only_unit_and_empty_are_level_polymorphic). Recorded in crates/kernel/DESIGN.md (Fragment) and docs/wf-former-design.md §1.1. Also recounted §8 of the ch07 doc: 13 type + 32 term formers at layer c = 45 branches, matching term.rs and BRANCH_DIMS. Honest caveat carried in §17: this is pen and paper like part I, and the transitivity/irrelevance cases for Wf were checked for shape against W's rather than written out — the composite spine recursion in transitivity is the one construction that appears twice and was written once. Full suite 311 passing.
