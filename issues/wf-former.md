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

## Status: phases 1–3 landed, phase 4 is next

| | Phase | State |
|---|---|---|
| 1 | `Vec` + `Fin` formers | **done** — commit `f538141`, `crates/kernel/tests/vec_fin.rs` (12) |
| 2 | `Wf` / `sup_f` / `elim_Wf` | **done** — commit `2ddd20b`, `crates/kernel/tests/wf.rs` (12) |
| 3 | codes + `rec.rs` branches; lifts the layer-c gate | **done** — `crates/kernel/tests/wf_codes.rs` (8) |
| 4 | ch. 07 logical relations | **next** — carries the only live falsifier |
| 5 | generator round (one regime) | pending — closes [[tier1-branching-constructors]] |

Full suite is at **309 passing**. Run it with `scripts/test` (never bare
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

## Phase 4: the falsifier

The ch. 07 logical-relations case for `Wf` is the **only** remaining thing
that could reopen the decision. Expected shape: the value clause is "labels
related and children componentwise related", a structural recursion over a
finite tuple — a *restriction* of `W`'s clause with the quantification over
subtree functions replaced by finitely many positions, so it should be
easier, not harder. `Vec`/`Fin` should reduce to cases on the whnf of the
length.

**Abort criterion, still live:** if that case needs a genuinely new idea
rather than a finitary restriction of `W`'s, reopen
[[tier1-branching-constructors]] with route A (`W` + funext) as the
considered fallback. `crates/elab/tests/branching_route_a.rs` is kept
unchanged precisely so that retreat stays costed and reproducible.

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
- **`Fin` is the sheddable piece** if phase 3 or 4 runs heavy: it never
  mentions `Wf`, so it could revert to an inlined `El (elim_Nat …)` schema
  (the n-ary prototype did exactly that and it worked). Nothing depends on
  `Fin` being primitive; it is there for goal readability and symmetry.
- **`Rose`-style nesting falls out of arity-as-a-term**: `Rose { Node(A,
  List Rose) }` is `Wf` with `S = Σ(a : A). Nat` and `n = snd x` — the child
  list *is* the `Vec`, its length is data in the shape. Worth exercising in
  phase 5.
- Watch de Bruijn indices in hand-built test terms: `App`'s `cod` binds its
  argument, so it sits one level deeper than the ambient. Both acceptance
  tests failed first on exactly that — in the test, not the kernel.

## Also in scope, decision-independent

`Empty`-η in `conv.rs` — cheap, plainly sound, improves the tier-2 `Acc`
story regardless of anything above. Not blocking.

## Log

- 2026-07-25: Phase 1 landed — Type::Vec and Type::Fin in the kernel. Reductions on the length (Vec(T;0)⇝Unit, Vec(T;S k)⇝Σ(_:T).Vec(T;k), Fin(0)⇝Empty, Fin(S k)⇝Unit+Fin(k)), neutral at a neutral length with structural congruence there; formation rules (Vec at its element's level, Fin at 0, length checked at Nat); no introduction/elimination forms — all eta is inherited through the reductions, which is the design's whole premise. Sites touched: term.rs (enum), subst.rs (length at same depth, no binder), reduce.rs (step_type + is_whnf_type/is_neutral_type keyed on whether the length is stuck + explicit beta_elim_ty block), typing.rs (formation + not_code_layer gate), conv.rs (neutral-length congruence + tm_nf neutral-type arm), fmt.rs. GATE: Vec/Fin are rejected at layer c until phase 3 gives them code formers and rec.rs branches, so boxed code stays exhaustively recursable; beta_elim_ty returns None (stuck) rather than mis-firing as belt-and-braces. Tests: crates/kernel/tests/vec_fin.rs (12), including sigma_eta_reaches_through_vec — for a NEUTRAL tuple cs : Vec(Nat;2), cs is convertible with its own projections repackaged, i.e. the equation route A needs funext for, discharged here by existing Sigma-eta + Unit-irrelevance. Also added Vec/Fin to the property-test type generator (common/mod.rs arms 16/17, >20/300 hit rate verified by test), so subst_laws/conv_properties/reduce now exercise them; full suite 289 passing.
- 2026-07-25: Phase 2 landed — Wf, sup_f, elim_Wf. Formation (Wf^l(x:S).n at level l — the arity is a Nat TERM with the shape free, so it contributes no level, unlike W whose positions are a type), introduction with Vec-tuple children, dependent elimination with the Fin-indexed ih, and the beta rule that synthesizes the ih lambda around the recursive call (same 'only beta rule that builds a binder' shape as elim_W's, but over a Fin index). nth is NOT a former: it is a fixed elim_Nat schema materialized by the rules (term::nth), and the step telescope is built once in term::wf_step_telescope and shared verbatim by typing.rs and conv.rs so the two transcriptions cannot drift — the hazard the design doc flagged. Sites: term.rs, subst.rs (arity binds one, motive one, step three), reduce.rs (beta + neutrality + whnf), typing.rs, conv.rs (Wf type congruence, sup_f value comparison at Vec type, elim_Wf neutral congruence), fmt.rs, tests/common (count + generators). Still layer-c gated until phase 3. ACCEPTANCE MET (crates/kernel/tests/wf.rs, 12 tests): Tree { Leaf, Node(Tree,Tree) } built on the real former, and mirror (mirror t) = t proved with every beta-marker deleted — the Leaf arm is literally refl_tree(leaf()) and the Node arm is cong + cong + trans, versus route A's funext-per-arm. sigma_eta_bridges_the_constructor_form pins the headline at the real former: for a NEUTRAL tuple cs, sup_f(inr u; cs) is convertible with node (nth 2 cs 0) (nth 2 cs 1). Two notes for phase 3: the motive is an ordinary Type binding z (no Ty-code round trip, unlike the postulate prototypes, since the eliminator is a former now), and Empty-eta turned out NOT to be needed for the Leaf arm — arity 0 is Vec(T;0) which reduces to Unit, whose proof irrelevance already collapses every nullary constructor form. Full suite 301 passing.
- 2026-07-25: Phase 3 landed — codes and the eight recursor branches; the layer-c gate is gone. New codes Term::TmVec/TmFin/TmWf with El decoding (only the element/shape decodes; the length and the arity are Nat terms and ride across unchanged). New branches ty_vec/tm_vec (1 univ, 3 globals, 2 locals), ty_fin/tm_fin (0/2/1), ty_wf/tm_wf (1/3/2), tm_supf (1/5/4), tm_elim_wf (2/6/5) — the last comparable to tm_elim_w but one universe shallower, its step binding built by wf_step_telescope so rec.rs/typing.rs/reduce.rs share one transcription. Sites: term.rs (3 variants + 8 Branches fields), rec.rs (branch_terms/branch_specs 37→45), subst.rs (code depths + map_branches), reduce.rs (El decoding, beta_elim_ty Vec/Fin/Wf replacing the None gate, beta_elim_tm TmVec/TmFin/TmWf/Supf/ElimWf, whnf classification), typing.rs (TmVec/TmFin/TmWf rules; not_code_layer deleted outright — it had no other users), conv.rs (congruence for the three codes), fmt.rs. Tests: crates/kernel/tests/wf_codes.rs (8) — El decoding, layer-c acceptance, and the identity recursor round-tripping box(Vec), box(Fin), box(Wf), box(TmVec/TmFin/TmWf), box(sup_f) and box(elim_Wf) in one β-step, which is the sharp cross-check of the new telescopes against reduce.rs's fire; plus a poisoned-branch negative and a generator-coverage check. BRANCH_DIMS is 45, identity_branches (both copies) grew eight hand-written arms, and both generators now reach the new formers — the scope-only one in common/mod.rs and, new here, the well-typed one in common/wt.rs (Vec/Fin/Wf types and TmVec/TmFin/TmWf encodings), so the subject-reduction and identity-recursor property suites cover them. Two incidental fixes fell out: scripts/test needs RUST_MIN_STACK=8M for the deeper telescope, and conv_pair_properties' 'η is not blind' negative moved to Σ(S, Nat) because a generated Vec(T;0) is genuinely proof-irrelevant. Full suite 309 passing.
